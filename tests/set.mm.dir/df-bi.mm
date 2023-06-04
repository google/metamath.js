

axiom df-bi(wph: 'wff' ph, wps: 'wff' ps) {

  return '|-' "-. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) )";
}
