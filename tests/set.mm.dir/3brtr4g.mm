include "wbr.mm"
include "breq12i.mm"
include "sylibr.mm"

theorem 3brtr4g
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume 3brtr4g.1: |- ( ph -> A R B )
  assume 3brtr4g.2: |- C = A
  assume 3brtr4g.3: |- D = B


  assert |- ( ph -> C R D )

  proof
    wph
    cA
    cB
    cR
    wbr
    cC
    cD
    cR
    wbr
    3brtr4g.1
    cC
    cA
    cD
    cB
    cR
    3brtr4g.2
    3brtr4g.3
    breq12i
    sylibr
end
