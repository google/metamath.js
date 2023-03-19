include "ccplgr.mm"
include "wcel.mm"
include "cvv.mm"
include "ciedg.mm"
include "cfv.mm"
include "cvtx.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "eqid.mm"
include "iscplgredg.mm"
include "crn.mm"
include "edgval.mm"
include "a1i.mm"
include "simpl.mm"
include "adantl.mm"
include "difeq1d.mm"
include "simpr.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "eqtr4d.mm"
include "rexeqdv.mm"
include "raleqbidv.mm"
include "biimpar.mm"
include "wb.mm"
include "vex.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "expcom.mm"
include "expd.mm"
include "syl5com.mm"
include "sylbid.mm"
include "pm2.43i.mm"
include "alrimiv.mm"
include "fvexd.mm"
include "gropeld.mm"

theorem cplgrop
  let cG: class G
  let ve: setvar e
  let vg: setvar g
  let vn: setvar n
  let vv: setvar v


  assert |- ( G e. ComplGraph -> <. ( Vtx ` G ) , ( iEdg ` G ) >. e. ComplGraph )

  proof
    cG
    ccplgr
    wcel
    #
    ccplgr
    cvv
    vg
    cG
    ciedg
    cfv
    #
    cG
    cvtx
    cfv
    #
    cvv
    @0
    vg
    cv
    #
    cvtx
    cfv
    #
    @2
    wceq
    #
    @3
    ciedg
    cfv
    #
    @1
    wceq
    #
    wa
    #
    @3
    ccplgr
    wcel
    #
    wi
    #
    vg
    @0
    @10
    @0
    @0
    vv
    cv
    #
    vn
    cv
    cpr
    ve
    cv
    wss
    #
    ve
    cG
    cedg
    cfv
    #
    wrex
    #
    vn
    @2
    @11
    csn
    #
    cdif
    #
    wral
    #
    vv
    @2
    wral
    #
    @10
    vv
    ve
    vn
    @13
    cG
    @2
    ccplgr
    @2
    eqid
    @13
    eqid
    iscplgredg
    @0
    @13
    @1
    crn
    #
    wceq
    #
    @18
    @10
    @20
    @0
    cG
    edgval
    a1i
    @18
    @20
    @8
    @9
    @20
    @8
    wa
    #
    @18
    @9
    @21
    @18
    wa
    @12
    ve
    @3
    cedg
    cfv
    #
    wrex
    #
    vn
    @4
    @15
    cdif
    #
    wral
    #
    vv
    @4
    wral
    #
    @9
    @21
    @26
    @18
    @21
    @25
    @17
    vv
    @4
    @2
    @8
    @5
    @20
    @5
    @7
    simpl
    #
    adantl
    @21
    @23
    @14
    vn
    @24
    @16
    @8
    @24
    @16
    wceq
    @20
    @8
    @4
    @2
    @15
    @27
    difeq1d
    adantl
    @21
    @12
    ve
    @22
    @13
    @21
    @22
    @19
    @13
    @8
    @22
    @19
    wceq
    @20
    @8
    @22
    @6
    crn
    @19
    @3
    edgval
    @8
    @6
    @1
    @5
    @7
    simpr
    rneqd
    syl5eq
    adantl
    @20
    @8
    simpl
    eqtr4d
    rexeqdv
    raleqbidv
    raleqbidv
    biimpar
    @3
    cvv
    wcel
    @9
    @26
    wb
    vg
    vex
    vv
    ve
    vn
    @22
    @3
    @4
    cvv
    @4
    eqid
    @22
    eqid
    iscplgredg
    ax-mp
    sylibr
    expcom
    expd
    syl5com
    sylbid
    pm2.43i
    alrimiv
    @0
    cG
    cvtx
    fvexd
    @0
    cG
    ciedg
    fvexd
    gropeld
end
