include "wtru.mm"
include "crab.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "cleqf.mm"
include "tru.mm"
include "rabid.mm"
include "mpbiran2.mm"
include "mpgbir.mm"

theorem bj-rabtrALT
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- { x e. A | T. } = A

  proof
    wtru
    vx
    cA
    crab
    #
    cA
    wceq
    vx
    cv
    #
    @0
    wcel
    #
    @1
    cA
    wcel
    #
    wb
    vx
    vx
    @0
    cA
    wtru
    vx
    cA
    nfrab1
    vx
    cA
    nfcv
    cleqf
    @2
    @3
    wtru
    tru
    wtru
    vx
    cA
    rabid
    mpbiran2
    mpgbir
end
