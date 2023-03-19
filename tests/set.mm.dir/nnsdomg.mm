include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "wn.mm"
include "csdm.mm"
include "wss.mm"
include "word.mm"
include "ordom.mm"
include "ordelss.mm"
include "mpan.mm"
include "ssdomg.mm"
include "syl5.mm"
include "imp.mm"
include "cfn.mm"
include "ominf.mm"
include "ensym.mm"
include "cv.mm"
include "wrex.mm"
include "breq2.mm"
include "rspcev.mm"
include "isfi.mm"
include "sylibr.mm"
include "ex.mm"
include "mtoi.mm"
include "adantl.mm"
include "brsdom.mm"
include "sylanbrc.mm"

theorem nnsdomg
  let cA: class A
  let vx: setvar x


  assert |- ( ( _om e. _V /\ A e. _om ) -> A ~< _om )

  proof
    com
    cvv
    wcel
    #
    cA
    com
    wcel
    #
    wa
    cA
    com
    cdom
    wbr
    #
    cA
    com
    cen
    wbr
    #
    wn
    #
    cA
    com
    csdm
    wbr
    @0
    @1
    @2
    @1
    cA
    com
    wss
    #
    @0
    @2
    com
    word
    @1
    @5
    ordom
    com
    cA
    ordelss
    mpan
    cA
    com
    cvv
    ssdomg
    syl5
    imp
    @1
    @4
    @0
    @1
    @3
    com
    cfn
    wcel
    #
    ominf
    @3
    com
    cA
    cen
    wbr
    #
    @1
    @6
    cA
    com
    ensym
    @1
    @7
    @6
    @1
    @7
    wa
    com
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    @6
    @9
    @7
    vx
    cA
    com
    @8
    cA
    com
    cen
    breq2
    rspcev
    vx
    com
    isfi
    sylibr
    ex
    syl5
    mtoi
    adantl
    cA
    com
    brsdom
    sylanbrc
end
