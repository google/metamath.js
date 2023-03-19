include "cgch.mm"
include "cvv.mm"
include "wceq.mm"
include "ccrd.mm"
include "cdm.mm"
include "wac.mm"
include "cv.mm"
include "wcel.mm"
include "com.mm"
include "cun.mm"
include "wss.mm"
include "cpw.mm"
include "cdom.mm"
include "wbr.mm"
include "vex.mm"
include "omex.mm"
include "unex.mm"
include "ssun2.mm"
include "ssdomg.mm"
include "mp2.mm"
include "a1i.mm"
include "id.mm"
include "syl5eleqr.mm"
include "pwex.mm"
include "gchacg.mm"
include "syl3anc.mm"
include "csdm.mm"
include "canth2.mm"
include "sdomdom.mm"
include "ax-mp.mm"
include "numdom.mm"
include "sylancl.mm"
include "ssun1.mm"
include "ssnum.mm"
include "2thd.mm"
include "eqrdv.mm"
include "dfac10.mm"
include "sylibr.mm"

theorem gchac
  let vx: setvar x


  assert |- ( GCH = _V -> CHOICE )

  proof
    cgch
    cvv
    wceq
    #
    ccrd
    cdm
    #
    cvv
    wceq
    wac
    @0
    vx
    @1
    cvv
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @2
    cvv
    wcel
    #
    @0
    @2
    com
    cun
    #
    @1
    wcel
    #
    @2
    @5
    wss
    @3
    @0
    @5
    cpw
    #
    @1
    wcel
    #
    @5
    @7
    cdom
    wbr
    #
    @6
    @0
    com
    @5
    cdom
    wbr
    #
    @5
    cgch
    wcel
    @7
    cgch
    wcel
    @8
    @10
    @0
    @5
    cvv
    wcel
    com
    @5
    wss
    @10
    @2
    com
    vx
    vex
    #
    omex
    unex
    #
    com
    @2
    ssun2
    com
    @5
    cvv
    ssdomg
    mp2
    a1i
    @0
    @5
    cvv
    cgch
    @12
    @0
    id
    #
    syl5eleqr
    @0
    @7
    cvv
    cgch
    @5
    @12
    pwex
    @13
    syl5eleqr
    @5
    gchacg
    syl3anc
    @5
    @7
    csdm
    wbr
    @9
    @5
    @12
    canth2
    @5
    @7
    sdomdom
    ax-mp
    @7
    @5
    numdom
    sylancl
    @2
    com
    ssun1
    @5
    @2
    ssnum
    sylancl
    @4
    @0
    @11
    a1i
    2thd
    eqrdv
    dfac10
    sylibr
end
