

axiom df-ex
  param wph: wff ph
  param vx: setvar x
  assert |- ( E. x ph <-> -. A. x -. ph )
end
