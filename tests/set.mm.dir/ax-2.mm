

axiom ax-2(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {

  return '|-' "( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )";
}
