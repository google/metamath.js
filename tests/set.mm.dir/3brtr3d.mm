include "wbr.mm"
include "breq12d.mm"
include "mpbid.mm"

theorem 3brtr3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume 3brtr3d.1: |- ( ph -> A R B )
  assume 3brtr3d.2: |- ( ph -> A = C )
  assume 3brtr3d.3: |- ( ph -> B = D )


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
    3brtr3d.1
    wph
    cA
    cC
    cB
    cD
    cR
    3brtr3d.2
    3brtr3d.3
    breq12d
    mpbid
end
