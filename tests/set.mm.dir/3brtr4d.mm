include "wbr.mm"
include "breq12d.mm"
include "mpbird.mm"

theorem 3brtr4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume 3brtr4d.1: |- ( ph -> A R B )
  assume 3brtr4d.2: |- ( ph -> C = A )
  assume 3brtr4d.3: |- ( ph -> D = B )


  assert |- ( ph -> C R D )

  proof
    wph
    cC
    cD
    cR
    wbr
    cA
    cB
    cR
    wbr
    3brtr4d.1
    wph
    cC
    cA
    cD
    cB
    cR
    3brtr4d.2
    3brtr4d.3
    breq12d
    mpbird
end
