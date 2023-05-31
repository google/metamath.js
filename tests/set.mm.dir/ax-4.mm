

axiom ax-4
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assert |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) )
end
