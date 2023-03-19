include "cusgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "csn.mm"
include "wex.mm"
include "c0.mm"
include "wa.mm"
include "ciedg.mm"
include "simpl.mm"
include "cvv.mm"
include "cvtx.mm"
include "wi.mm"
include "vex.mm"
include "a1i.mm"
include "eqeq1i.mm"
include "biimpi.mm"
include "adantl.mm"
include "usgr1vr.mm"
include "3adant1.mm"
include "syl3anc.mm"
include "mpd.mm"
include "cedg.mm"
include "wb.mm"
include "cuhgr.mm"
include "usgruhgr.mm"
include "uhgriedg0edg0.mm"
include "syl.mm"
include "adantr.mm"
include "syl5bb.mm"
include "mpbird.mm"
include "ex.mm"
include "exlimdv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hash1snb.mm"
include "mp1i.mm"
include "hasheq0.mm"
include "3imtr4d.mm"
include "imp.mm"

theorem usgr1v0e
  let cE: class E
  let cG: class G
  let cV: class V
  let ve: setvar e
  let cN: class N
  let vv: setvar v
  assume fusgredgfi.v: |- V = ( Vtx ` G )
  assume fusgredgfi.e: |- E = ( Edg ` G )


  assert |- ( ( G e. USGraph /\ ( # ` V ) = 1 ) -> ( # ` E ) = 0 )

  proof
    cG
    cusgr
    wcel
    #
    cV
    chash
    cfv
    c1
    wceq
    #
    cE
    chash
    cfv
    cc0
    wceq
    #
    @0
    cV
    vv
    cv
    #
    csn
    #
    wceq
    #
    vv
    wex
    #
    cE
    c0
    wceq
    #
    @1
    @2
    @0
    @5
    @7
    vv
    @0
    @5
    @7
    @0
    @5
    wa
    #
    @7
    cG
    ciedg
    cfv
    c0
    wceq
    #
    @8
    @0
    @9
    @0
    @5
    simpl
    #
    @8
    @0
    @3
    cvv
    wcel
    #
    cG
    cvtx
    cfv
    #
    @4
    wceq
    #
    @0
    @9
    wi
    #
    @10
    @11
    @8
    vv
    vex
    a1i
    @5
    @13
    @0
    @5
    @13
    cV
    @12
    @4
    fusgredgfi.v
    eqeq1i
    biimpi
    adantl
    @11
    @13
    @14
    @0
    @3
    cG
    cvv
    usgr1vr
    3adant1
    syl3anc
    mpd
    @7
    cG
    cedg
    cfv
    #
    c0
    wceq
    #
    @8
    @9
    cE
    @15
    c0
    fusgredgfi.e
    eqeq1i
    @0
    @16
    @9
    wb
    #
    @5
    @0
    cG
    cuhgr
    wcel
    @17
    cG
    usgruhgr
    cG
    uhgriedg0edg0
    syl
    adantr
    syl5bb
    mpbird
    ex
    exlimdv
    cV
    cvv
    wcel
    @1
    @6
    wb
    @0
    cV
    @12
    cvv
    fusgredgfi.v
    cG
    cvtx
    fvex
    eqeltri
    cV
    cvv
    vv
    hash1snb
    mp1i
    cE
    cvv
    wcel
    @2
    @7
    wb
    @0
    cE
    @15
    cvv
    fusgredgfi.e
    cG
    cedg
    fvex
    eqeltri
    cE
    cvv
    hasheq0
    mp1i
    3imtr4d
    imp
end
