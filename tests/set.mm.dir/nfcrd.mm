include "wnfc.mm"
include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "nfcr.mm"
include "syl.mm"

theorem nfcrd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume nfeqd.1: |- ( ph -> F/_ x A )

  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ph -> F/ x y e. A )

  proof
    wph
    vx
    cA
    wnfc
    vy
    cv
    cA
    wcel
    vx
    wnf
    nfeqd.1
    vx
    vy
    cA
    nfcr
    syl
end
