include "cin.mm"
include "c0.mm"
include "incom.mm"
include "syl5eqner.mm"
include "xpcogend.mm"

theorem xpcoidgend
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xpcoidgend.1: |- ( ph -> ( A i^i B ) =/= (/) )


  assert |- ( ph -> ( ( A X. B ) o. ( A X. B ) ) = ( A X. B ) )

  proof
    wph
    cA
    cB
    cA
    cB
    wph
    cB
    cA
    cin
    cA
    cB
    cin
    c0
    cA
    cB
    incom
    xpcoidgend.1
    syl5eqner
    xpcogend
end
