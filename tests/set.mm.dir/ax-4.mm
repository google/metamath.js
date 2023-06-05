

axiom ax-4(wph: wff ph, wps: wff ps, vx: setvar x) {

  return |- "( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) )";
}
