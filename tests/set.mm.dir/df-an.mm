

axiom df-an(wph: 'wff' ph, wps: 'wff' ps) {

  return '|-' "( ( ph /\\ ps ) <-> -. ( ph -> -. ps ) )";
}
