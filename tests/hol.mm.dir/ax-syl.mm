

axiom ax-syl(tr: 'term' R, ts: 'term' S, tt: 'term' T) {
  assume ax-syl.1: |- "R |= S";
  assume ax-syl.2: |- "S |= T";

  return '|-' "R |= T";
}
