
axiom df-bnj17
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ( ph /\ ps /\ ch ) /\ th ) )
end
