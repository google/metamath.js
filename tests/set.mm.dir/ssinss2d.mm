include "cin.mm"
include "incom.mm"
include "ssinss1d.mm"
include "syl5eqss.mm"

theorem ssinss2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ssinss2d.1: |- ( ph -> B C_ C )


  assert |- ( ph -> ( A i^i B ) C_ C )

  proof
    wph
    cA
    cB
    cin
    cB
    cA
    cin
    cC
    cA
    cB
    incom
    wph
    cB
    cA
    cC
    ssinss2d.1
    ssinss1d
    syl5eqss
end
