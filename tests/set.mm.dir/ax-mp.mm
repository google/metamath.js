

axiom ax-mp(wph: 'wff' ph, wps: 'wff' ps) {
  assume min: |- "ph";
  assume maj: |- "( ph -> ps )";

  return '|-' "ps";
}
