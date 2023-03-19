
axiom df-ifp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assert |- ( if- ( ph , ps , ch ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) )
end
