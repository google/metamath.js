include "cin.mm"
include "wcel.mm"
include "elinel1.mm"
include "syl.mm"

theorem elin1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cX: class X
  assume elin1d.1: |- ( ph -> X e. ( A i^i B ) )


  assert |- ( ph -> X e. A )

  proof
    wph
    cX
    cA
    cB
    cin
    wcel
    cX
    cA
    wcel
    elin1d.1
    cX
    cA
    cB
    elinel1
    syl
end
