include "wcel.mm"
include "wf1.mm"
include "w3a.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "cvv.mm"
include "wf.mm"
include "f1f.mm"
include "fex2.mm"
include "syl3an1.mm"
include "3coml.mm"
include "simp3.mm"
include "f1eq1.mm"
include "spcegv.mm"
include "sylc.mm"
include "wb.mm"
include "brdomg.mm"
include "3ad2ant2.mm"
include "mpbird.mm"

theorem f1dom2g
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  let vf: setvar f


  assert |- ( ( A e. V /\ B e. W /\ F : A -1-1-> B ) -> A ~<_ B )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cA
    cB
    cF
    wf1
    #
    w3a
    #
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    vf
    cv
    #
    wf1
    #
    vf
    wex
    #
    @3
    cF
    cvv
    wcel
    #
    @2
    @7
    @2
    @0
    @1
    @8
    @2
    cA
    cB
    cF
    wf
    @0
    @1
    @8
    cA
    cB
    cF
    f1f
    cA
    cB
    cF
    cV
    cW
    fex2
    syl3an1
    3coml
    @0
    @1
    @2
    simp3
    @6
    @2
    vf
    cF
    cvv
    cA
    cB
    @5
    cF
    f1eq1
    spcegv
    sylc
    @1
    @0
    @4
    @7
    wb
    @2
    cA
    cB
    cW
    vf
    brdomg
    3ad2ant2
    mpbird
end
