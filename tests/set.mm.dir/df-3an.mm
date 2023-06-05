

axiom df-3an(wph: wff ph, wps: wff ps, wch: wff ch) {

  return |- "( ( ph /\\ ps /\\ ch ) <-> ( ( ph /\\ ps ) /\\ ch ) )";
}
