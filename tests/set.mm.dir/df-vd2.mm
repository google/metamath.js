
axiom df-vd2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assert |- ( (. ph ,. ps ->. ch ). <-> ( ( ph /\ ps ) -> ch ) )
end
