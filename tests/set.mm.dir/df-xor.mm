
axiom df-xor
  let wph: wff ph
  let wps: wff ps
  assert |- ( ( ph \/_ ps ) <-> -. ( ph <-> ps ) )
end
