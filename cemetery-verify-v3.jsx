import { useState, useEffect, useRef, useCallback, useMemo } from "react";

/* ═══════════════════════════════════════════
   BINARY PARSERS
   ═══════════════════════════════════════════ */
function parseSHP(buf) {
  const dv = new DataView(buf);
  if (dv.getInt32(0, false) !== 9994) throw new Error("Invalid SHP");
  const feats = [];
  let off = 100;
  while (off < buf.byteLength - 8) {
    const recLen = dv.getInt32(off + 4, false) * 2;
    const rs = off + 8;
    if (rs + 4 > buf.byteLength) break;
    const st = dv.getInt32(rs, true);
    if (st === 5 || st === 15) {
      const nParts = dv.getInt32(rs + 36, true);
      const nPts = dv.getInt32(rs + 40, true);
      const parts = [];
      for (let i = 0; i < nParts; i++) parts.push(dv.getInt32(rs + 44 + i * 4, true));
      const po = rs + 44 + nParts * 4;
      const rings = [];
      for (let p = 0; p < nParts; p++) {
        const s = parts[p], e = p + 1 < nParts ? parts[p + 1] : nPts;
        const ring = [];
        for (let i = s; i < e; i++) ring.push([dv.getFloat64(po + i * 16, true), dv.getFloat64(po + i * 16 + 8, true)]);
        rings.push(ring);
      }
      feats.push({ type: "Polygon", rings });
    } else if (st === 1 || st === 11) {
      feats.push({ type: "Point", x: dv.getFloat64(rs + 4, true), y: dv.getFloat64(rs + 12, true) });
    } else {
      feats.push({ type: "Null" });
    }
    off += 8 + recLen;
  }
  return feats;
}

function parseCSV(text) {
  const lines = text.split(/\r?\n/).filter(l => l.trim());
  if (lines.length < 2) return [];
  const parseRow = (line) => {
    const vals = []; let cur = ""; let inQ = false;
    for (let i = 0; i < line.length; i++) {
      const c = line[i];
      if (c === '"') { if (inQ && line[i + 1] === '"') { cur += '"'; i++; } else inQ = !inQ; }
      else if (c === ',' && !inQ) { vals.push(cur.trim()); cur = ""; }
      else cur += c;
    }
    vals.push(cur.trim());
    return vals;
  };
  const headers = parseRow(lines[0]);
  return lines.slice(1).map(l => {
    const vals = parseRow(l);
    const obj = {};
    headers.forEach((h, i) => obj[h] = vals[i] || "");
    return obj;
  });
}

async function readZip(file) {
  const buf = await file.arrayBuffer();
  const dv = new DataView(buf);
  const files = {};
  let off = 0;
  while (off < buf.byteLength - 4) {
    if (dv.getUint32(off, true) !== 0x04034b50) break;
    const comp = dv.getUint16(off + 8, true);
    const cSize = dv.getUint32(off + 18, true);
    const uSize = dv.getUint32(off + 22, true);
    const nLen = dv.getUint16(off + 26, true);
    const eLen = dv.getUint16(off + 28, true);
    const name = new TextDecoder().decode(new Uint8Array(buf, off + 30, nLen));
    const dataStart = off + 30 + nLen + eLen;
    const ext = name.split(".").pop().toLowerCase();
    if (["shp", "dbf", "csv"].includes(ext)) {
      if (comp === 0) {
        files[ext] = { buf: buf.slice(dataStart, dataStart + cSize), text: ext === "csv" ? new TextDecoder().decode(new Uint8Array(buf, dataStart, cSize)) : null };
      } else if (comp === 8) {
        try {
          const raw = new Uint8Array(buf, dataStart, cSize);
          const ds = new DecompressionStream("deflate-raw");
          const w = ds.writable.getWriter();
          w.write(raw); w.close();
          const r = ds.readable.getReader();
          const chunks = [];
          while (true) { const { done, value } = await r.read(); if (done) break; chunks.push(value); }
          const total = chunks.reduce((a, c) => a + c.length, 0);
          const result = new Uint8Array(total);
          let p = 0; for (const ch of chunks) { result.set(ch, p); p += ch.length; }
          files[ext] = { buf: result.buffer, text: ext === "csv" ? new TextDecoder().decode(result) : null };
        } catch { /* skip compressed file we can't decompress */ }
      }
    }
    off = dataStart + cSize;
  }
  return files;
}

/* ═══════════════════════════════════════════
   GEO UTILS
   ═══════════════════════════════════════════ */
function pip(x, y, ring) {
  let inside = false;
  for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
    const [xi, yi] = ring[i], [xj, yj] = ring[j];
    if (((yi > y) !== (yj > y)) && (x < (xj - xi) * (y - yi) / (yj - yi) + xi)) inside = !inside;
  }
  return inside;
}
function centroid(ring) {
  let sx = 0, sy = 0; for (const [x, y] of ring) { sx += x; sy += y; }
  return [sx / ring.length, sy / ring.length];
}
function normLot(l) { const n = parseInt(l, 10); return isNaN(n) ? String(l).trim() : String(n); }

/* ═══════════════════════════════════════════
   CRC32 + ZIP BUILDER (for photo export)
   ═══════════════════════════════════════════ */
const crcTable = (() => {
  const t = new Uint32Array(256);
  for (let i = 0; i < 256; i++) { let c = i; for (let j = 0; j < 8; j++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1); t[i] = c; }
  return t;
})();
function crc32(data) {
  let c = 0xFFFFFFFF;
  for (let i = 0; i < data.length; i++) c = crcTable[(c ^ data[i]) & 0xFF] ^ (c >>> 8);
  return (c ^ 0xFFFFFFFF) >>> 0;
}
function buildZip(files) {
  const enc = new TextEncoder();
  const locals = [], centrals = [];
  let off = 0;
  for (const f of files) {
    const nb = enc.encode(f.name);
    const crc = crc32(f.data);
    const lh = new Uint8Array(30 + nb.length + f.data.length);
    const ld = new DataView(lh.buffer);
    ld.setUint32(0, 0x04034b50, true);
    ld.setUint16(4, 20, true); ld.setUint16(8, 0, true);
    ld.setUint32(14, crc, true);
    ld.setUint32(18, f.data.length, true);
    ld.setUint32(22, f.data.length, true);
    ld.setUint16(26, nb.length, true);
    lh.set(nb, 30); lh.set(f.data, 30 + nb.length);
    locals.push(lh);
    const ch = new Uint8Array(46 + nb.length);
    const cd = new DataView(ch.buffer);
    cd.setUint32(0, 0x02014b50, true);
    cd.setUint16(4, 20, true); cd.setUint16(6, 20, true);
    cd.setUint32(16, crc, true);
    cd.setUint32(20, f.data.length, true);
    cd.setUint32(24, f.data.length, true);
    cd.setUint16(28, nb.length, true);
    cd.setUint32(42, off, true);
    ch.set(nb, 46);
    centrals.push(ch);
    off += lh.length;
  }
  const cdSize = centrals.reduce((a, c) => a + c.length, 0);
  const eocd = new Uint8Array(22);
  const ed = new DataView(eocd.buffer);
  ed.setUint32(0, 0x06054b50, true);
  ed.setUint16(8, files.length, true); ed.setUint16(10, files.length, true);
  ed.setUint32(12, cdSize, true); ed.setUint32(16, off, true);
  const total = off + cdSize + 22;
  const out = new Uint8Array(total);
  let p = 0;
  for (const l of locals) { out.set(l, p); p += l.length; }
  for (const c of centrals) { out.set(c, p); p += c.length; }
  out.set(eocd, p);
  return out;
}
function base64ToUint8(b64) {
  const bin = atob(b64);
  const u8 = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) u8[i] = bin.charCodeAt(i);
  return u8;
}

/* ═══════════════════════════════════════════
   MAIN APP
   ═══════════════════════════════════════════ */
export default function CemeteryV3() {
  const [plots, setPlots] = useState([]); // { geometry, attrs, centroid }
  const [loaded, setLoaded] = useState(false);
  const [fieldMap, setFieldMap] = useState(null); // maps our keys to actual field names
  const [availableFields, setAvailableFields] = useState([]);

  const [view, setView] = useState("upload");
  const [searchText, setSearchText] = useState("");
  const [selPlotIdx, setSelPlotIdx] = useState(null);
  const [selSection, setSelSection] = useState(null);
  const [selLot, setSelLot] = useState(null);
  const [toast, setToast] = useState("");
  const [sessionLog, setSessionLog] = useState([]);
  const [discNote, setDiscNote] = useState("");
  const [photos, setPhotos] = useState({}); // { "A-1-5": dataUrl }
  const [capturedPhoto, setCapturedPhoto] = useState(null);
  const [cameraActive, setCameraActive] = useState(false);
  const [highlightedIdx, setHighlightedIdx] = useState(null);
  const [tempMap, setTempMap] = useState({});

  const [gps, setGps] = useState(null);
  const [gpsAcc, setGpsAcc] = useState(null);
  const [avgDuration, setAvgDuration] = useState(10); // seconds
  const [averaging, setAveraging] = useState(null); // { samples: [{lat,lng,acc}], startTime, timer }
  const [capturedCoords, setCapturedCoords] = useState({}); // { "A-1-5": { lat, lng, acc, samples, duration } }
  const gpsRef = useRef(null);
  const avgRef = useRef(null); // interval ref for averaging
  const avgSamplesRef = useRef([]); // mutable sample buffer
  const fileRef = useRef(null);
  const videoRef = useRef(null);
  const canvasRef = useRef(null);
  const streamRef = useRef(null);

  // Toast
  useEffect(() => { if (toast) { const t = setTimeout(() => setToast(""), 3000); return () => clearTimeout(t); } }, [toast]);

  // Sync tempMap when fieldMap changes (auto-detection)
  useEffect(() => { if (fieldMap) setTempMap(fieldMap); }, [fieldMap]);

  // GPS
  const startGPS = useCallback(() => {
    if (!navigator.geolocation) return;
    gpsRef.current = navigator.geolocation.watchPosition(
      (p) => { setGps({ lat: p.coords.latitude, lng: p.coords.longitude }); setGpsAcc(p.coords.accuracy); },
      () => {}, { enableHighAccuracy: true, maximumAge: 1000, timeout: 15000 }
    );
  }, []);
  useEffect(() => () => { if (gpsRef.current != null) navigator.geolocation.clearWatch(gpsRef.current); }, []);

  // GPS → highlight plot
  useEffect(() => {
    if (!gps || !plots.length) return;
    for (let i = 0; i < plots.length; i++) {
      if (plots[i].geometry?.type === "Polygon" && pip(gps.lng, gps.lat, plots[i].geometry.rings[0])) {
        setHighlightedIdx(i); return;
      }
    }
    setHighlightedIdx(null);
  }, [gps, plots]);

  // ── GPS Averaging ──
  const startAveraging = useCallback((pid) => {
    if (!gps) return setToast("No GPS signal");
    avgSamplesRef.current = [{ lat: gps.lat, lng: gps.lng, acc: gpsAcc }];
    const startTime = Date.now();
    setAveraging({ startTime, sampleCount: 1, elapsed: 0, pid });
    avgRef.current = setInterval(() => {
      const elapsed = (Date.now() - startTime) / 1000;
      const samples = avgSamplesRef.current;
      setAveraging(prev => prev ? { ...prev, sampleCount: samples.length, elapsed } : null);
      if (elapsed >= avgDuration) {
        clearInterval(avgRef.current);
        avgRef.current = null;
        if (samples.length > 0) {
          const avgLat = samples.reduce((s, p) => s + p.lat, 0) / samples.length;
          const avgLng = samples.reduce((s, p) => s + p.lng, 0) / samples.length;
          const avgAcc = samples.reduce((s, p) => s + p.acc, 0) / samples.length;
          const spreads = samples.map(p => {
            const dLat = (p.lat - avgLat) * 111320;
            const dLng = (p.lng - avgLng) * 111320 * Math.cos(avgLat * Math.PI / 180);
            return Math.sqrt(dLat * dLat + dLng * dLng);
          });
          const maxSpread = Math.max(...spreads);
          setCapturedCoords(prev => ({ ...prev, [pid]: { lat: avgLat, lng: avgLng, acc: avgAcc, spread: maxSpread, samples: samples.length, duration: avgDuration } }));
          setToast(`GPS captured: ${samples.length} samples, ±${maxSpread < 1 ? (maxSpread * 100).toFixed(1) + "cm" : maxSpread.toFixed(2) + "m"} spread`);
        }
        setAveraging(null);
        avgSamplesRef.current = [];
      }
    }, 200);
  }, [gps, gpsAcc, avgDuration]);

  const stopAveraging = useCallback(() => {
    if (avgRef.current) { clearInterval(avgRef.current); avgRef.current = null; }
    setAveraging(prev => {
      if (!prev) return null;
      const samples = avgSamplesRef.current;
      if (samples.length >= 2) {
        const avgLat = samples.reduce((s, p) => s + p.lat, 0) / samples.length;
        const avgLng = samples.reduce((s, p) => s + p.lng, 0) / samples.length;
        const avgAcc = samples.reduce((s, p) => s + p.acc, 0) / samples.length;
        const spreads = samples.map(p => {
          const dLat = (p.lat - avgLat) * 111320;
          const dLng = (p.lng - avgLng) * 111320 * Math.cos(avgLat * Math.PI / 180);
          return Math.sqrt(dLat * dLat + dLng * dLng);
        });
        const maxSpread = Math.max(...spreads);
        const elapsed = (Date.now() - prev.startTime) / 1000;
        setCapturedCoords(pc => ({ ...pc, [prev.pid]: { lat: avgLat, lng: avgLng, acc: avgAcc, spread: maxSpread, samples: samples.length, duration: Math.round(elapsed) } }));
        setToast(`Stopped: ${samples.length} samples saved`);
      }
      return null;
    });
    avgSamplesRef.current = [];
  }, []);

  // Push GPS samples during averaging
  useEffect(() => {
    if (averaging && gps) {
      avgSamplesRef.current.push({ lat: gps.lat, lng: gps.lng, acc: gpsAcc || 99 });
    }
  }, [gps, averaging]);

  // Cleanup averaging on unmount
  useEffect(() => () => { if (avgRef.current) clearInterval(avgRef.current); }, []);

  // ── Auto-detect field mapping ──
  const detectFields = useCallback((fields) => {
    const uf = fields.map(f => f.toUpperCase());
    const find = (...candidates) => {
      for (const c of candidates) { const i = uf.indexOf(c.toUpperCase()); if (i >= 0) return fields[i]; }
      return null;
    };
    const map = {
      section: find("SECTION", "Sec", "SECT"),
      lot: find("LOT", "Lot"),
      plot: find("PLOT", "Plot", "GRAVE"),
      firstName: find("BURIALFIRST", "FIRST_NAME", "FIRSTNAME", "FIRST", "BURIALFIRS"),
      middleName: find("BURIALMIDDLE", "MIDDLE_NAME", "MIDDLENAME", "MIDDLE", "BURIALMID"),
      lastName: find("BURIALLAST", "LAST_NAME", "LASTNAME", "LAST", "BURIALLAS"),
      birth: find("BIRTH", "BIRTHDATE", "BORN", "DOB"),
      death: find("DEATH", "DEATHDATE", "DIED", "DOD"),
      owner: find("OWNERNAME", "OWNER", "OWNER_NAME"),
      spouse: find("SPOUSE"),
      epitaph: find("EPITAPH"),
      military: find("ISMILITARY", "MILITARY", "MIL"),
      burialType: find("BURIALTYPE", "BURIAL_TYPE", "TYPE"),
      saleStatus: find("SALESTATUS", "SALE_STATUS", "STATUS"),
      notes: find("NOTES"),
      discrepancy: find("DISCREPANCY_NOTES", "DISCREPANC", "DISC_NOTES"),
      findagrave: find("FINDAGRAVE_URL", "FINDAGRAVE", "FAG_URL"),
      aka: find("AKA"),
      nickname: find("NICKNAME"),
    };
    return map;
  }, []);

  const getField = useCallback((attrs, key) => {
    if (!fieldMap || !fieldMap[key]) return "";
    return String(attrs[fieldMap[key]] || "").trim();
  }, [fieldMap]);

  const plotId = useCallback((attrs) => {
    const s = getField(attrs, "section");
    const l = normLot(getField(attrs, "lot"));
    const p = getField(attrs, "plot");
    return `${s}-${l}-${p}`;
  }, [getField]);

  const fullName = useCallback((attrs) => {
    return [getField(attrs, "firstName"), getField(attrs, "middleName"), getField(attrs, "lastName")].filter(Boolean).join(" ") || "(empty plot)";
  }, [getField]);

  const hasName = useCallback((attrs) => !!getField(attrs, "firstName") || !!getField(attrs, "lastName"), [getField]);

  // ── Load shapefile ZIP ──
  const handleFile = useCallback(async (e) => {
    const file = e.target.files?.[0]; if (!file) return;
    try {
      setToast("Parsing shapefile...");
      const z = await readZip(file);
      if (!z.shp) { setToast("No .shp file found in ZIP"); return; }
      const shapes = parseSHP(z.shp.buf);

      let records = [];
      if (z.csv?.text) {
        records = parseCSV(z.csv.text);
        setToast(`Parsed CSV: ${records.length} records`);
      }
      if (records.length === 0) {
        setToast("No CSV found in ZIP. Export from Diamond Maps includes a CSV alongside the SHP — make sure it's in the ZIP.");
        return;
      }

      const fields = Object.keys(records[0] || {});
      setAvailableFields(fields);
      const fMap = detectFields(fields);
      setFieldMap(fMap);

      const plotData = [];
      for (let i = 0; i < Math.min(shapes.length, records.length); i++) {
        const g = shapes[i]; if (g.type === "Null") continue;
        const c = g.type === "Polygon" ? centroid(g.rings[0]) : g.type === "Point" ? [g.x, g.y] : null;
        plotData.push({ geometry: g, attrs: records[i], centroid: c, idx: i });
      }
      setPlots(plotData);
      setLoaded(true);
      startGPS();
      setView(fMap.section && fMap.lot && fMap.plot ? "map" : "fields");
      setToast(`Loaded ${plotData.length} plots`);
    } catch (err) { setToast("Error: " + err.message); }
  }, [detectFields, startGPS]);

  // ── Camera ──
  const startCamera = useCallback(async () => {
    try {
      const stream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: "environment", width: { ideal: 2048 }, height: { ideal: 1536 } } });
      streamRef.current = stream;
      if (videoRef.current) { videoRef.current.srcObject = stream; videoRef.current.play(); }
      setCameraActive(true);
    } catch (err) { setToast("Camera: " + err.message); }
  }, []);
  const stopCamera = useCallback(() => {
    if (streamRef.current) { streamRef.current.getTracks().forEach(t => t.stop()); streamRef.current = null; }
    setCameraActive(false);
  }, []);
  const capturePhoto = useCallback(() => {
    if (!videoRef.current || !canvasRef.current) return;
    const v = videoRef.current, c = canvasRef.current;
    c.width = v.videoWidth; c.height = v.videoHeight;
    c.getContext("2d").drawImage(v, 0, 0);
    const dataUrl = c.toDataURL("image/jpeg", 0.88);
    setCapturedPhoto(dataUrl);
    stopCamera();
  }, [stopCamera]);

  // ── Save photo for plot ──
  const savePhoto = useCallback((attrs, dataUrl) => {
    const id = plotId(attrs);
    setPhotos(prev => ({ ...prev, [id]: dataUrl }));
    setToast(`Photo saved: ${id}.jpg`);
  }, [plotId]);

  // ── Download all photos as ZIP ──
  const downloadPhotos = useCallback(() => {
    const entries = Object.entries(photos);
    if (!entries.length) return setToast("No photos to download");
    const files = entries.map(([id, dataUrl]) => ({
      name: `${id}.jpg`,
      data: base64ToUint8(dataUrl.split(",")[1]),
    }));
    const zip = buildZip(files);
    const blob = new Blob([zip], { type: "application/zip" });
    const a = document.createElement("a"); a.href = URL.createObjectURL(blob);
    a.download = `headstone_photos_${new Date().toISOString().slice(0, 10)}.zip`; a.click();
    setToast(`Downloaded ${files.length} photos`);
  }, [photos]);

  // ── Session log ──
  const logEntry = useCallback((attrs, status, notes) => {
    const pid = plotId(attrs);
    const avg = capturedCoords[pid];
    const useLat = avg ? avg.lat : (gps?.lat || "");
    const useLng = avg ? avg.lng : (gps?.lng || "");
    const useAcc = avg ? avg.acc : (gpsAcc || "");
    setSessionLog(prev => [...prev, {
      ts: new Date().toISOString(), id: pid, section: getField(attrs, "section"),
      lot: getField(attrs, "lot"), plot: getField(attrs, "plot"), name: fullName(attrs),
      status, notes, lat: useLat, lng: useLng, acc: useAcc,
      avgSamples: avg?.samples || 0, avgSpread: avg?.spread || "",
      hasPhoto: !!photos[pid] || !!capturedPhoto,
    }]);
    setToast(`${status}: ${pid}`);
  }, [plotId, getField, fullName, gps, gpsAcc, photos, capturedPhoto, capturedCoords]);

  const getLogStatus = useCallback((attrs) => {
    const id = plotId(attrs);
    const e = sessionLog.findLast(e => e.id === id);
    return e?.status || null;
  }, [sessionLog, plotId]);

  // ── Export CSV ──
  const exportCSV = useCallback(() => {
    if (!sessionLog.length) return setToast("Nothing to export");
    const h = "TIMESTAMP,GRAVE_ID,SECTION,LOT,PLOT,NAME,STATUS,NOTES,LATITUDE,LONGITUDE,ACCURACY_M,AVG_SAMPLES,AVG_SPREAD_M,HAS_PHOTO";
    const rows = sessionLog.map(e =>
      [e.ts, e.id, e.section, e.lot, e.plot, `"${e.name}"`, e.status, `"${(e.notes||"").replace(/"/g,'""')}"`, e.lat, e.lng, e.acc, e.avgSamples || 0, e.avgSpread || "", e.hasPhoto].join(",")
    );
    const blob = new Blob([h + "\n" + rows.join("\n")], { type: "text/csv" });
    const a = document.createElement("a"); a.href = URL.createObjectURL(blob);
    a.download = `diamond_maps_session_${new Date().toISOString().slice(0, 10)}.csv`; a.click();
  }, [sessionLog]);

  // ── Navigation data ──
  const sections = useMemo(() => {
    const s = new Set(plots.map(p => getField(p.attrs, "section")).filter(Boolean));
    return [...s].sort((a, b) => { const na = parseInt(a), nb = parseInt(b); return !isNaN(na) && !isNaN(nb) ? na - nb : a.localeCompare(b); });
  }, [plots, getField]);

  const lotsForSection = useMemo(() => {
    if (!selSection) return [];
    const ls = new Set(plots.filter(p => getField(p.attrs, "section") === selSection).map(p => normLot(getField(p.attrs, "lot"))));
    return [...ls].sort((a, b) => { const na = parseFloat(a), nb = parseFloat(b); return !isNaN(na) && !isNaN(nb) ? na - nb : a.localeCompare(b); });
  }, [plots, selSection, getField]);

  const plotsForLot = useMemo(() => {
    if (!selSection || selLot === null) return [];
    return plots.filter(p => getField(p.attrs, "section") === selSection && normLot(getField(p.attrs, "lot")) === selLot)
      .sort((a, b) => (Number(getField(a.attrs, "plot")) || 0) - (Number(getField(b.attrs, "plot")) || 0));
  }, [plots, selSection, selLot, getField]);

  const searchResults = useMemo(() => {
    if (!searchText || searchText.length < 2) return [];
    const q = searchText.toLowerCase();
    return plots.filter(p => {
      const n = fullName(p.attrs).toLowerCase();
      const loc = plotId(p.attrs).toLowerCase();
      const ow = getField(p.attrs, "owner").toLowerCase();
      return n.includes(q) || loc.includes(q) || ow.includes(q);
    }).slice(0, 30);
  }, [plots, searchText, fullName, plotId, getField]);

  // ── Map bounds ──
  const mapBounds = useMemo(() => {
    if (!plots.length) return null;
    let xn = Infinity, xx = -Infinity, yn = Infinity, yx = -Infinity;
    for (const p of plots) { if (!p.centroid) continue; const [x, y] = p.centroid; if (x < xn) xn = x; if (x > xx) xx = x; if (y < yn) yn = y; if (y > yx) yx = y; }
    const pad = 0.0003;
    return { xn: xn - pad, xx: xx + pad, yn: yn - pad, yx: yx + pad };
  }, [plots]);

  // ── Colors ──
  const C = { bg: "#06090f", card: "#0e1420", bdr: "#172032", acc: "#0091ff", grn: "#00c853", org: "#ff9100", red: "#d50000", purp: "#7c4dff", txt: "#e0e8f0", dim: "#556677", vdim: "#334455" };
  const gpsColor = gpsAcc === null ? C.vdim : gpsAcc < 0.05 ? C.grn : gpsAcc < 1 ? "#2e7d32" : gpsAcc < 5 ? C.org : C.red;
  const gpsLabel = gpsAcc === null ? "NO GPS" : gpsAcc < 0.05 ? "RTK FIX" : gpsAcc < 1 ? `±${(gpsAcc*100).toFixed(0)}cm` : `±${gpsAcc.toFixed(1)}m`;

  // ── Common UI parts ──
  const Btn = ({ bg, full, children, ...p }) => (
    <button {...p} style={{ background: bg || C.acc, color: "#fff", border: "none", borderRadius: 10, padding: "13px 18px", fontSize: 14, fontWeight: 600, cursor: "pointer", fontFamily: "inherit", width: full ? "100%" : "auto", textAlign: "center", display: "inline-flex", alignItems: "center", justifyContent: "center", gap: 6, WebkitAppearance: "none", ...(p.style || {}) }}>{children}</button>
  );
  const GpsChip = () => <span style={{ fontSize: 10, padding: "4px 10px", borderRadius: 12, fontWeight: 700, background: gpsColor, color: "#fff", whiteSpace: "nowrap" }}>{gpsLabel}</span>;
  const Header = ({ title, back }) => (
    <div style={{ background: C.card, borderBottom: `1px solid ${C.bdr}`, padding: "12px 16px", display: "flex", alignItems: "center", justifyContent: "space-between", position: "sticky", top: 0, zIndex: 100 }}>
      {back ? <button onClick={back} style={{ background: "none", border: "none", color: C.acc, fontSize: 14, fontWeight: 700, cursor: "pointer", fontFamily: "inherit" }}>← Back</button> : <span style={{ fontSize: 14, fontWeight: 700, color: C.acc, letterSpacing: 1.5 }}>{title}</span>}
      {back && <span style={{ fontSize: 13, fontWeight: 700, color: C.dim }}>{title}</span>}
      <GpsChip />
    </div>
  );
  const Tag = ({ bg, children }) => <span style={{ display: "inline-block", background: bg, color: "#fff", fontSize: 10, padding: "2px 8px", borderRadius: 10, fontWeight: 700, marginRight: 4, letterSpacing: 0.5 }}>{children}</span>;
  const Label = ({ children }) => <div style={{ fontSize: 10, color: C.dim, textTransform: "uppercase", letterSpacing: 1.2, marginBottom: 4, fontWeight: 600 }}>{children}</div>;
  const Card = ({ children, borderColor, ...p }) => <div style={{ background: C.card, border: `1px solid ${C.bdr}`, borderRadius: 10, padding: 14, marginBottom: 10, borderLeft: borderColor ? `3px solid ${borderColor}` : undefined, ...(p.style || {}) }}>{children}</div>;
  const BottomNav = () => (
    <div style={{ position: "fixed", bottom: 0, left: "50%", transform: "translateX(-50%)", width: "100%", maxWidth: 480, background: C.card, borderTop: `1px solid ${C.bdr}`, display: "flex", zIndex: 100, paddingBottom: "env(safe-area-inset-bottom, 0)" }}>
      {[{ v: "map", icon: "🗺", label: "Map" }, { v: "nav", icon: "📍", label: "Nav" }, { v: "search", icon: "🔍", label: "Search" },
        { v: "session", icon: "📋", label: `${sessionLog.length}` }].map(n => (
        <button key={n.v} onClick={() => setView(n.v)} style={{ flex: 1, padding: "10px 4px", background: "transparent", border: "none", color: view === n.v ? C.acc : C.dim, fontSize: 10, fontWeight: 600, cursor: "pointer", fontFamily: "inherit", borderTop: view === n.v ? `2px solid ${C.acc}` : "2px solid transparent" }}>
          {n.icon} {n.label}
        </button>
      ))}
    </div>
  );
  const Toast = () => toast ? <div style={{ position: "fixed", top: 64, left: "50%", transform: "translateX(-50%)", background: C.acc, color: "#fff", padding: "10px 24px", borderRadius: 12, fontSize: 13, fontWeight: 600, zIndex: 200, boxShadow: "0 4px 24px rgba(0,145,255,0.3)" }}>{toast}</div> : null;

  const PlotRow = ({ p, onClick }) => {
    const hn = hasName(p.attrs);
    const dn = getField(p.attrs, "discrepancy");
    const ls = getLogStatus(p.attrs);
    const photoExists = !!photos[plotId(p.attrs)];
    return (
      <div onClick={onClick} style={{ background: ls === "VERIFIED" ? "#081808" : ls === "DISCREPANCY" ? "#180c00" : C.card, borderLeft: `3px solid ${ls === "VERIFIED" ? C.grn : ls === "DISCREPANCY" ? C.org : dn ? C.org : hn ? C.acc : C.vdim}`, padding: "12px 14px", marginBottom: 6, borderRadius: 10, cursor: "pointer", display: "flex", justifyContent: "space-between", alignItems: "center" }}>
        <div style={{ flex: 1 }}>
          <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
            <span style={{ fontWeight: hn ? 600 : 400, fontSize: 14, color: hn ? C.txt : C.vdim }}>{fullName(p.attrs)}</span>
            {dn && <Tag bg={C.org}>!</Tag>}
            {getField(p.attrs, "military") && <Tag bg="#1b5e20">MIL</Tag>}
            {photoExists && <span style={{ fontSize: 11, color: C.dim }}>📷</span>}
          </div>
          <div style={{ fontSize: 11, color: C.dim, marginTop: 2 }}>
            {plotId(p.attrs)} {getField(p.attrs, "birth") && `· ${getField(p.attrs, "birth")}`} {getField(p.attrs, "death") && `— ${getField(p.attrs, "death")}`}
          </div>
        </div>
        <span style={{ color: C.vdim, fontSize: 18 }}>›</span>
      </div>
    );
  };

  // ═════════════ UPLOAD VIEW ═════════════
  if (view === "upload") {
    return (
      <div style={{ fontFamily: "'SF Pro Text', -apple-system, sans-serif", background: C.bg, color: C.txt, minHeight: "100vh", maxWidth: 480, margin: "0 auto", padding: 24, paddingTop: 48 }}>
        <div style={{ textAlign: "center", marginBottom: 32 }}>
          <div style={{ fontSize: 36, marginBottom: 8 }}>⛏</div>
          <div style={{ fontSize: 18, fontWeight: 800, color: C.acc, letterSpacing: 2.5 }}>CEMETERY VERIFY</div>
          <div style={{ fontSize: 12, color: C.dim, marginTop: 4 }}>Teton / Newdale · v3</div>
        </div>
        <Card style={{ padding: 22, border: `2px dashed ${C.bdr}`, textAlign: "center" }}>
          <div style={{ fontSize: 13, color: C.dim, marginBottom: 14, lineHeight: 1.6 }}>
            Export your plot layer from Diamond Maps as a shapefile ZIP (with pre-joined interment data)
          </div>
          <input ref={fileRef} type="file" accept=".zip" onChange={handleFile} style={{ display: "none" }} />
          <Btn bg={C.acc} full onClick={() => fileRef.current?.click()}>Load Diamond Maps Export (.zip)</Btn>
          <div style={{ fontSize: 11, color: C.vdim, marginTop: 12, lineHeight: 1.5, textAlign: "left" }}>
            Menu → Export → SHP file → download ZIP
            <br />ZIP must contain .shp + .csv files
          </div>
        </Card>
        <div style={{ marginTop: 28, fontSize: 11, color: C.vdim, lineHeight: 1.9 }}>
          <div style={{ fontWeight: 700, color: C.dim, letterSpacing: 1, marginBottom: 4 }}>SETUP</div>
          <div>✓ Interment data joined to plots in Diamond Maps</div>
          <div>✓ Emlid RS4 Pro paired via Bluetooth</div>
          <div>✓ NTRIP running on RS4 → RTK corrections</div>
          <div>✓ iOS picks up RTK position automatically</div>
        </div>
        <Toast />
      </div>
    );
  }

  // ═════════════ FIELD MAPPING VIEW ═════════════
  if (view === "fields") {
    const keys = ["section", "lot", "plot", "firstName", "lastName", "birth", "death", "epitaph"];
    const labels = { section: "Section", lot: "Lot", plot: "Plot", firstName: "First Name", lastName: "Last Name", birth: "Birth Date", death: "Death Date", epitaph: "Epitaph" };
    return (
      <div style={{ fontFamily: "'SF Pro Text', -apple-system, sans-serif", background: C.bg, color: C.txt, minHeight: "100vh", maxWidth: 480, margin: "0 auto", padding: 16 }}>
        <div style={{ fontSize: 14, fontWeight: 700, color: C.org, marginBottom: 12, letterSpacing: 1 }}>MAP YOUR FIELDS</div>
        <div style={{ fontSize: 12, color: C.dim, marginBottom: 16, lineHeight: 1.5 }}>
          Match your Diamond Maps fields to the expected data. Only Section, Lot, Plot are required.
        </div>
        {keys.map(k => (
          <div key={k} style={{ marginBottom: 10 }}>
            <Label>{labels[k]}{["section","lot","plot"].includes(k) ? " *" : ""}</Label>
            <select value={tempMap[k] || ""} onChange={e => setTempMap(p => ({ ...p, [k]: e.target.value }))}
              style={{ width: "100%", padding: "10px 12px", background: "#0a0f18", border: `1px solid ${C.bdr}`, borderRadius: 8, color: C.txt, fontSize: 14, fontFamily: "inherit" }}>
              <option value="">— none —</option>
              {availableFields.map(f => <option key={f} value={f}>{f}</option>)}
            </select>
          </div>
        ))}
        <Btn bg={C.acc} full onClick={() => { setFieldMap(tempMap); setView("map"); }} style={{ marginTop: 12 }}>
          Continue →
        </Btn>
        <Toast />
      </div>
    );
  }

  const APP = { fontFamily: "'SF Pro Text', -apple-system, BlinkMacSystemFont, sans-serif", background: C.bg, color: C.txt, minHeight: "100vh", maxWidth: 480, margin: "0 auto" };

  // ═════════════ MAP VIEW ═════════════
  if (view === "map") {
    const W = 460, H = 460;
    const { xn, xx, yn, yx } = mapBounds || { xn: 0, xx: 1, yn: 0, yx: 1 };
    const sc = Math.min(W / (xx - xn), H / (yx - yn)) * 0.92;
    const toS = (lng, lat) => [(lng - xn) * sc + 16, H - (lat - yn) * sc - 16];
    const nearPlot = highlightedIdx !== null ? plots[highlightedIdx] : null;

    return (
      <div style={APP}>
        <Header title="PLOT MAP" />
        <div style={{ padding: 12, paddingBottom: 90 }}>
          <svg viewBox={`0 0 ${W} ${H}`} style={{ width: "100%", background: "#040810", borderRadius: 12, border: `1px solid ${C.bdr}` }}>
            {plots.map((p, i) => {
              if (p.geometry?.type !== "Polygon") return null;
              const pts = p.geometry.rings[0].map(([x, y]) => toS(x, y).join(",")).join(" ");
              const hn = hasName(p.attrs);
              const ls = getLogStatus(p.attrs);
              const isHl = highlightedIdx === i;
              let fill = hn ? "#0c1828" : "#0a0f16";
              if (ls === "VERIFIED") fill = "#082008";
              else if (ls === "DISCREPANCY") fill = "#201000";
              return <polygon key={i} points={pts} fill={isHl ? "rgba(0,145,255,0.3)" : fill}
                stroke={isHl ? C.acc : ls === "VERIFIED" ? C.grn : ls === "DISCREPANCY" ? C.org : hn ? "#142840" : "#101820"}
                strokeWidth={isHl ? 2.5 : 0.6} style={{ cursor: "pointer" }}
                onClick={() => { setSelPlotIdx(i); setView("detail"); setCapturedPhoto(null); setDiscNote(""); }} />;
            })}
            {gps && (() => {
              const [gx, gy] = toS(gps.lng, gps.lat);
              if (gx < -40 || gx > W + 40 || gy < -40 || gy > H + 40) return null;
              return <g>
                <circle cx={gx} cy={gy} r={12} fill="rgba(0,145,255,0.12)"><animate attributeName="r" values="8;15;8" dur="2s" repeatCount="indefinite" /></circle>
                <circle cx={gx} cy={gy} r={4.5} fill={C.acc} stroke="#fff" strokeWidth={1.5} />
              </g>;
            })()}
          </svg>

          {nearPlot && (
            <Card borderColor={C.acc} style={{ marginTop: 10, cursor: "pointer" }}
              onClick={() => { setSelPlotIdx(highlightedIdx); setView("detail"); setCapturedPhoto(null); setDiscNote(""); }}>
              <div style={{ fontSize: 10, color: C.acc, fontWeight: 700, letterSpacing: 1 }}>YOU ARE HERE</div>
              <div style={{ fontSize: 18, fontWeight: 700, marginTop: 2 }}>{fullName(nearPlot.attrs)}</div>
              <div style={{ fontSize: 12, color: C.dim, marginTop: 2 }}>
                {plotId(nearPlot.attrs)} {getField(nearPlot.attrs, "birth") && `· ${getField(nearPlot.attrs, "birth")}`} {getField(nearPlot.attrs, "death") && `— ${getField(nearPlot.attrs, "death")}`}
              </div>
              {getField(nearPlot.attrs, "discrepancy") && <div style={{ background: "#2a1800", border: `1px solid ${C.org}`, borderRadius: 6, padding: 8, marginTop: 6, fontSize: 12, color: "#ffcc80" }}>⚠ {getField(nearPlot.attrs, "discrepancy")}</div>}
            </Card>
          )}

          <div style={{ display: "flex", gap: 8, marginTop: 10 }}>
            {[{ l: "PLOTS", v: plots.length, c: C.acc }, { l: "VERIFIED", v: sessionLog.filter(e => e.status === "VERIFIED").length, c: C.grn }, { l: "GPS", v: Object.keys(capturedCoords).length, c: "#00b0ff" }, { l: "PHOTOS", v: Object.keys(photos).length, c: C.purp }].map((s, i) => (
              <Card key={i} style={{ flex: 1, textAlign: "center", padding: 10 }}>
                <div style={{ fontSize: 20, fontWeight: 800, color: s.c }}>{s.v}</div>
                <div style={{ fontSize: 9, color: C.dim, letterSpacing: 1, fontWeight: 600 }}>{s.l}</div>
              </Card>
            ))}
          </div>
        </div>
        <BottomNav />
        <Toast />
      </div>
    );
  }

  // ═════════════ DETAIL VIEW ═════════════
  if (view === "detail" && selPlotIdx !== null) {
    const p = plots[selPlotIdx];
    if (!p) { setView("map"); return null; }
    const a = p.attrs;
    const empty = !hasName(a);
    const ls = getLogStatus(a);
    const pid = plotId(a);
    const existingPhoto = photos[pid];

    return (
      <div style={APP}>
        <Header title={pid} back={() => { setView(plots.length > 0 ? "map" : "nav"); setSelPlotIdx(null); setCapturedPhoto(null); setDiscNote(""); stopCamera(); stopAveraging(); }} />
        <div style={{ padding: 14, paddingBottom: 30 }}>
          {/* Identity */}
          <Card borderColor={ls === "VERIFIED" ? C.grn : ls === "DISCREPANCY" ? C.org : empty ? C.vdim : C.acc}>
            <div style={{ display: "flex", gap: 4, marginBottom: 6, flexWrap: "wrap" }}>
              {ls && <Tag bg={ls === "VERIFIED" ? C.grn : C.org}>{ls}</Tag>}
              {getField(a, "military") && <Tag bg="#1b5e20">MILITARY</Tag>}
              {getField(a, "burialType") && <Tag bg={C.purp}>{getField(a, "burialType").toUpperCase()}</Tag>}
              {getField(a, "saleStatus") && <Tag bg={C.vdim}>{getField(a, "saleStatus")}</Tag>}
              {getField(a, "discrepancy") && <Tag bg={C.org}>DISCREPANCY</Tag>}
              {existingPhoto && <Tag bg={C.purp}>📷 PHOTO</Tag>}
            </div>
            <div style={{ fontSize: 22, fontWeight: 800, color: empty ? C.dim : "#fff" }}>{fullName(a)}</div>
            {getField(a, "aka") && <div style={{ fontSize: 13, color: C.dim }}>AKA: {getField(a, "aka")}</div>}
            {getField(a, "nickname") && <div style={{ fontSize: 13, color: C.dim }}>"{getField(a, "nickname")}"</div>}
          </Card>

          {/* Dates */}
          {!empty && (
            <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 8, marginBottom: 8 }}>
              <Card><Label>Born</Label><div style={{ fontSize: 15, fontWeight: 500 }}>{getField(a, "birth") || "—"}</div></Card>
              <Card><Label>Died</Label><div style={{ fontSize: 15, fontWeight: 500 }}>{getField(a, "death") || "—"}</div></Card>
            </div>
          )}

          {(getField(a, "spouse") || getField(a, "owner")) && (
            <Card>
              {getField(a, "spouse") && <><Label>Spouse</Label><div style={{ fontSize: 14, marginBottom: 6 }}>{getField(a, "spouse")}</div></>}
              {getField(a, "owner") && <><Label>Lot Owner</Label><div style={{ fontSize: 14 }}>{getField(a, "owner")}</div></>}
            </Card>
          )}

          {getField(a, "epitaph") && <Card><Label>Epitaph</Label><div style={{ fontSize: 14, fontStyle: "italic", lineHeight: 1.5 }}>{getField(a, "epitaph")}</div></Card>}
          {getField(a, "discrepancy") && <div style={{ background: "#2a1800", border: `1px solid ${C.org}`, borderRadius: 10, padding: 12, marginBottom: 10, fontSize: 13, color: "#ffcc80", lineHeight: 1.5 }}>⚠ {getField(a, "discrepancy")}</div>}

          {/* GPS CAPTURE WITH AVERAGING */}
          <div style={{ fontSize: 10, fontWeight: 700, color: C.dim, letterSpacing: 1.5, marginBottom: 8, marginTop: 4 }}>GPS CAPTURE</div>
          {(() => {
            const savedCoord = capturedCoords[pid];
            const isAveraging = !!averaging;
            const progress = isAveraging ? Math.min(averaging.elapsed / avgDuration, 1) : 0;

            return (
              <Card borderColor={savedCoord ? C.grn : isAveraging ? C.acc : C.vdim}>
                {/* Live position */}
                {gps && (
                  <div style={{ marginBottom: 10 }}>
                    <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center" }}>
                      <Label>Live Position</Label>
                      <span style={{ fontSize: 10, color: gpsColor, fontWeight: 700 }}>{gpsLabel}</span>
                    </div>
                    <div style={{ fontSize: 12, color: "#81d4fa", fontFamily: "monospace" }}>
                      {gps.lat.toFixed(8)}, {gps.lng.toFixed(8)}
                    </div>
                  </div>
                )}
                {!gps && <div style={{ fontSize: 13, color: C.org, padding: 8 }}>Waiting for GPS signal...</div>}

                {/* Duration selector */}
                {!isAveraging && (
                  <div style={{ marginBottom: 10 }}>
                    <Label>Averaging Duration</Label>
                    <div style={{ display: "flex", gap: 6, marginTop: 4 }}>
                      {[5, 10, 15, 30, 60].map(sec => (
                        <button key={sec} onClick={() => setAvgDuration(sec)}
                          style={{ flex: 1, padding: "8px 4px", background: avgDuration === sec ? C.acc : "#080d16", border: `1px solid ${avgDuration === sec ? C.acc : C.bdr}`, borderRadius: 8, color: avgDuration === sec ? "#fff" : C.dim, fontSize: 12, fontWeight: 600, cursor: "pointer", fontFamily: "inherit" }}>
                          {sec}s
                        </button>
                      ))}
                    </div>
                  </div>
                )}

                {/* Averaging in progress */}
                {isAveraging && (
                  <div style={{ marginBottom: 10 }}>
                    {/* Progress bar */}
                    <div style={{ width: "100%", height: 6, background: "#0a1020", borderRadius: 3, overflow: "hidden", marginBottom: 8 }}>
                      <div style={{ width: `${progress * 100}%`, height: "100%", background: C.acc, borderRadius: 3, transition: "width 0.2s" }} />
                    </div>
                    <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center" }}>
                      <div>
                        <span style={{ fontSize: 24, fontWeight: 800, color: C.acc }}>{averaging.sampleCount}</span>
                        <span style={{ fontSize: 12, color: C.dim, marginLeft: 4 }}>samples</span>
                      </div>
                      <div style={{ textAlign: "right" }}>
                        <span style={{ fontSize: 18, fontWeight: 700, color: C.txt }}>{Math.ceil(avgDuration - averaging.elapsed)}s</span>
                        <span style={{ fontSize: 11, color: C.dim, marginLeft: 4 }}>remaining</span>
                      </div>
                    </div>
                  </div>
                )}

                {/* Saved coordinates */}
                {savedCoord && !isAveraging && (
                  <div style={{ background: "#081808", border: `1px solid ${C.grn}`, borderRadius: 8, padding: 10, marginBottom: 10 }}>
                    <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: 4 }}>
                      <span style={{ fontSize: 10, fontWeight: 700, color: C.grn, letterSpacing: 1 }}>✓ CAPTURED</span>
                      <span style={{ fontSize: 10, color: C.dim }}>{savedCoord.samples} samples / {savedCoord.duration}s</span>
                    </div>
                    <div style={{ fontSize: 13, color: "#81d4fa", fontFamily: "monospace" }}>
                      {savedCoord.lat.toFixed(8)}, {savedCoord.lng.toFixed(8)}
                    </div>
                    <div style={{ fontSize: 11, color: C.dim, marginTop: 2 }}>
                      Avg accuracy: {savedCoord.acc < 1 ? (savedCoord.acc * 100).toFixed(1) + "cm" : savedCoord.acc.toFixed(2) + "m"}
                      {" · "}Spread: {savedCoord.spread < 1 ? (savedCoord.spread * 100).toFixed(1) + "cm" : savedCoord.spread.toFixed(3) + "m"}
                    </div>
                  </div>
                )}

                {/* Capture / Stop buttons */}
                {!isAveraging ? (
                  <div style={{ display: "flex", gap: 8 }}>
                    <Btn bg={gps ? C.acc : C.vdim} full onClick={() => gps && startAveraging(pid)} style={{ opacity: gps ? 1 : 0.5 }}>
                      📍 {savedCoord ? "Re-capture" : "Capture"} GPS ({avgDuration}s)
                    </Btn>
                  </div>
                ) : (
                  <Btn bg={C.org} full onClick={stopAveraging}>⏹ Stop Early ({averaging.sampleCount} samples)</Btn>
                )}
              </Card>
            );
          })()}

          {/* Links */}
          {getField(a, "findagrave") && (
            <a href={getField(a, "findagrave")} target="_blank" rel="noreferrer" style={{ color: C.acc, fontSize: 13, fontWeight: 600, display: "block", marginBottom: 12 }}>FindAGrave →</a>
          )}

          {/* ═══ HEADSTONE PHOTO ═══ */}
          <div style={{ fontSize: 10, fontWeight: 700, color: C.dim, letterSpacing: 1.5, marginBottom: 8, marginTop: 4 }}>HEADSTONE PHOTO</div>
          <canvas ref={canvasRef} style={{ display: "none" }} />
          <Card borderColor={existingPhoto ? C.purp : C.vdim}>
            {!cameraActive && !capturedPhoto && !existingPhoto && (
              <Btn bg="#1565c0" full onClick={startCamera}>📷 Take Headstone Photo</Btn>
            )}
            {!cameraActive && !capturedPhoto && existingPhoto && (
              <>
                <img src={existingPhoto} alt="headstone" style={{ width: "100%", borderRadius: 8, marginBottom: 8 }} />
                <Btn bg="#1565c0" onClick={startCamera}>📷 Retake</Btn>
              </>
            )}
            {cameraActive && (
              <>
                <video ref={videoRef} style={{ width: "100%", borderRadius: 8, marginBottom: 8 }} playsInline autoPlay muted />
                <div style={{ display: "flex", gap: 8 }}>
                  <Btn bg={C.grn} onClick={capturePhoto}>📸 Snap</Btn>
                  <Btn bg={C.vdim} onClick={stopCamera}>Cancel</Btn>
                </div>
              </>
            )}
            {capturedPhoto && !cameraActive && (
              <>
                <img src={capturedPhoto} alt="headstone" style={{ width: "100%", borderRadius: 8, marginBottom: 8 }} />
                <div style={{ display: "flex", gap: 8 }}>
                  <Btn bg="#1565c0" onClick={() => { setCapturedPhoto(null); startCamera(); }}>Retake</Btn>
                  <Btn bg={C.grn} onClick={() => savePhoto(a, capturedPhoto)}>💾 Save Photo</Btn>
                </div>
              </>
            )}
          </Card>

          {/* Notes */}
          <Card>
            <Label>Field Notes</Label>
            <textarea style={{ background: "#080d16", border: `1px solid ${C.bdr}`, borderRadius: 8, padding: 12, color: C.txt, fontSize: 14, width: "100%", fontFamily: "inherit", boxSizing: "border-box", minHeight: 60, resize: "vertical", WebkitAppearance: "none" }}
              value={discNote} onChange={e => setDiscNote(e.target.value)} placeholder="What differs from the headstone?" />
          </Card>

          {/* Actions */}
          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 8 }}>
            <Btn bg={C.grn} full onClick={() => { if (capturedPhoto && !photos[pid]) savePhoto(a, capturedPhoto); logEntry(a, "VERIFIED", discNote); setDiscNote(""); }}>✓ Verified</Btn>
            <Btn bg={C.org} full onClick={() => { if (capturedPhoto && !photos[pid]) savePhoto(a, capturedPhoto); logEntry(a, "DISCREPANCY", discNote); setDiscNote(""); }}>⚠ Discrepancy</Btn>
            <Btn bg={C.acc} full onClick={() => { logEntry(a, "GPS_ONLY", discNote); setDiscNote(""); }}>📍 GPS Only</Btn>
            <Btn bg={C.purp} full onClick={() => { logEntry(a, "NOT_FOUND", discNote); setDiscNote(""); }}>✗ Not Found</Btn>
          </div>
        </div>
        <Toast />
      </div>
    );
  }

  // ═════════════ SESSION VIEW ═════════════
  if (view === "session") {
    const photoCount = Object.keys(photos).length;
    return (
      <div style={APP}>
        <Header title="SESSION" />
        <div style={{ padding: 14, paddingBottom: 90 }}>
          <div style={{ display: "flex", gap: 8, marginBottom: 14, flexWrap: "wrap" }}>
            <Btn bg={C.acc} onClick={exportCSV}>📄 Export CSV</Btn>
            {photoCount > 0 && <Btn bg={C.purp} onClick={downloadPhotos}>📷 Photos ZIP ({photoCount})</Btn>}
          </div>
          {!sessionLog.length && <div style={{ textAlign: "center", color: C.dim, padding: 32 }}>No entries yet. Go verify some headstones!</div>}
          {[...sessionLog].reverse().map((e, i) => (
            <Card key={i} borderColor={e.status === "VERIFIED" ? C.grn : e.status === "DISCREPANCY" ? C.org : e.status === "GPS_ONLY" ? C.acc : C.purp}>
              <div style={{ display: "flex", justifyContent: "space-between" }}>
                <span style={{ fontWeight: 600, fontSize: 14 }}>{e.name || e.id}</span>
                <Tag bg={e.status === "VERIFIED" ? C.grn : e.status === "DISCREPANCY" ? C.org : e.status === "GPS_ONLY" ? C.acc : C.purp}>{e.status}</Tag>
              </div>
              <div style={{ fontSize: 11, color: C.dim, marginTop: 4 }}>
                {e.id} · {new Date(e.ts).toLocaleTimeString()}
                {e.lat && ` · ${parseFloat(e.lat).toFixed(6)}, ${parseFloat(e.lng).toFixed(6)}`}
                {e.avgSamples > 0 && ` · ${e.avgSamples} avg`}
                {e.hasPhoto && " · 📷"}
              </div>
              {e.notes && <div style={{ fontSize: 12, color: C.txt, marginTop: 4 }}>{e.notes}</div>}
            </Card>
          ))}
        </div>
        <BottomNav />
        <Toast />
      </div>
    );
  }

  // ═════════════ SEARCH VIEW ═════════════
  if (view === "search") {
    return (
      <div style={APP}>
        <Header title="SEARCH" />
        <div style={{ padding: 14, paddingBottom: 90 }}>
          <input style={{ background: "#080d16", border: `1px solid ${C.bdr}`, borderRadius: 10, padding: "13px 14px", color: C.txt, fontSize: 17, width: "100%", fontFamily: "inherit", boxSizing: "border-box", WebkitAppearance: "none", marginBottom: 12 }}
            placeholder="Name, owner, or location..." value={searchText} onChange={e => setSearchText(e.target.value)} autoFocus />
          {searchResults.map((p, i) => (
            <PlotRow key={i} p={p} onClick={() => { setSelPlotIdx(p.idx); setView("detail"); setCapturedPhoto(null); setDiscNote(""); }} />
          ))}
          {searchText.length >= 2 && !searchResults.length && <div style={{ textAlign: "center", color: C.dim, padding: 24 }}>No results</div>}
        </div>
        <BottomNav />
        <Toast />
      </div>
    );
  }

  // ═════════════ NAV VIEW ═════════════
  return (
    <div style={APP}>
      <Header title="NAVIGATE" />
      <div style={{ padding: 14, paddingBottom: 90 }}>
        <Label>SECTION</Label>
        <div style={{ display: "grid", gridTemplateColumns: `repeat(${Math.min(sections.length, 6)}, 1fr)`, gap: 6, marginBottom: 14, marginTop: 4 }}>
          {sections.map(s => (
            <button key={s} onClick={() => { setSelSection(s === selSection ? null : s); setSelLot(null); }}
              style={{ background: selSection === s ? C.acc : C.card, border: `1px solid ${selSection === s ? C.acc : C.bdr}`, borderRadius: 10, padding: "14px 6px", color: selSection === s ? "#fff" : C.dim, fontSize: 16, fontWeight: 700, cursor: "pointer", fontFamily: "inherit" }}>
              {s}
            </button>
          ))}
        </div>
        {selSection && (
          <>
            <Label>LOT — Section {selSection}</Label>
            <div style={{ display: "grid", gridTemplateColumns: "repeat(6, 1fr)", gap: 4, maxHeight: 200, overflowY: "auto", marginBottom: 14, marginTop: 4 }}>
              {lotsForSection.map(l => (
                <button key={l} onClick={() => setSelLot(l === selLot ? null : l)}
                  style={{ background: selLot === l ? C.acc : "#080d16", border: `1px solid ${selLot === l ? C.acc : C.bdr}`, borderRadius: 8, padding: "10px 4px", color: selLot === l ? "#fff" : C.dim, fontSize: 13, fontWeight: 600, cursor: "pointer", fontFamily: "inherit" }}>
                  {l}
                </button>
              ))}
            </div>
          </>
        )}
        {selSection && selLot !== null && (
          <>
            <Label>PLOTS — {selSection}-{selLot}</Label>
            <div style={{ marginTop: 4 }}>
              {plotsForLot.map((p, i) => (
                <PlotRow key={i} p={p} onClick={() => { setSelPlotIdx(p.idx); setView("detail"); setCapturedPhoto(null); setDiscNote(""); }} />
              ))}
            </div>
          </>
        )}
      </div>
      <BottomNav />
      <Toast />
    </div>
  );
}
