include "nic-swap.mm"

theorem nic-bijust
  let wta: wff ta


  assert |- ( ( ta -/\ ta ) -/\ ( ( ta -/\ ta ) -/\ ( ta -/\ ta ) ) )

  proof
    wta
    wta
    nic-swap
end
