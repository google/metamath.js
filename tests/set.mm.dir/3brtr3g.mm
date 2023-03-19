include "wbr.mm"
include "breq12i.mm"
include "sylib.mm"

theorem 3brtr3g
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume 3brtr3g.1: |- ( ph -> A R B )
  assume 3brtr3g.2: |- A = C
  assume 3brtr3g.3: |- B = D


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
    3brtr3g.1
    cA
    cC
    cB
    cD
    cR
    3brtr3g.2
    3brtr3g.3
    breq12i
    sylib
end
