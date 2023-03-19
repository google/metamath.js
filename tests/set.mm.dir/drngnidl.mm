include "cdr.mm"
include "wcel.mm"
include "csn.mm"
include "cpr.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "simpr.mm"
include "orcd.mm"
include "wne.mm"
include "cur.mm"
include "cfv.mm"
include "wrex.mm"
include "crg.mm"
include "drngring.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "lidlnz.mm"
include "syl3anc.mm"
include "wel.mm"
include "cinvr.mm"
include "cmulr.mm"
include "co.mm"
include "simpll.mm"
include "wss.mm"
include "lidlss.mm"
include "adantl.mm"
include "sselda.mm"
include "adantrr.mm"
include "simprr.mm"
include "eqid.mm"
include "drnginvrl.mm"
include "drnginvrcl.mm"
include "simprl.mm"
include "lidlmcl.mm"
include "syl22anc.mm"
include "eqeltrrd.mm"
include "rexlimdvaa.mm"
include "imp.mm"
include "syldan.mm"
include "wb.mm"
include "lidl1el.mm"
include "sylan.mm"
include "adantr.mm"
include "mpbid.mm"
include "olcd.mm"
include "pm2.61dane.mm"
include "vex.mm"
include "elpr.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "lidl0.mm"
include "lidl1.mm"
include "snex.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "prss.mm"
include "bicomi.mm"
include "sylanbrc.mm"
include "syl.mm"
include "eqssd.mm"

theorem drngnidl
  let cB: class B
  let cR: class R
  let cU: class U
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  assume drngnidl.b: |- B = ( Base ` R )
  assume drngnidl.z: |- .0. = ( 0g ` R )
  assume drngnidl.u: |- U = ( LIdeal ` R )


  assert |- ( R e. DivRing -> U = { { .0. } , B } )

  proof
    cR
    cdr
    wcel
    #
    cU
    c.0
    csn
    #
    cB
    cpr
    #
    @0
    va
    cU
    @2
    @0
    va
    cv
    #
    cU
    wcel
    #
    @3
    @2
    wcel
    #
    @0
    @4
    wa
    #
    @3
    @1
    wceq
    #
    @3
    cB
    wceq
    #
    wo
    #
    @5
    @6
    @9
    @3
    @1
    @6
    @7
    wa
    @7
    @8
    @6
    @7
    simpr
    orcd
    @6
    @3
    @1
    wne
    #
    wa
    #
    @8
    @7
    @11
    cR
    cur
    cfv
    #
    @3
    wcel
    #
    @8
    @6
    @10
    vb
    cv
    #
    c.0
    wne
    #
    vb
    @3
    wrex
    #
    @13
    @11
    cR
    crg
    wcel
    #
    @4
    @10
    @16
    @0
    @17
    @4
    @10
    cR
    drngring
    #
    ad2antrr
    @0
    @4
    @10
    simplr
    @6
    @10
    simpr
    vb
    cR
    cU
    @3
    c.0
    drngnidl.u
    drngnidl.z
    lidlnz
    syl3anc
    @6
    @16
    @13
    @6
    @15
    @13
    vb
    @3
    @6
    vb
    va
    wel
    #
    @15
    wa
    #
    wa
    #
    @14
    cR
    cinvr
    cfv
    #
    cfv
    #
    @14
    cR
    cmulr
    cfv
    #
    co
    #
    @12
    @3
    @21
    @0
    @14
    cB
    wcel
    #
    @15
    @25
    @12
    wceq
    @0
    @4
    @20
    simpll
    #
    @6
    @19
    @26
    @15
    @6
    @3
    cB
    @14
    @4
    @3
    cB
    wss
    @0
    cB
    @3
    cU
    cR
    drngnidl.b
    drngnidl.u
    lidlss
    adantl
    sselda
    adantrr
    #
    @6
    @19
    @15
    simprr
    #
    cB
    cR
    @24
    @12
    @22
    @14
    c.0
    drngnidl.b
    drngnidl.z
    @24
    eqid
    #
    @12
    eqid
    #
    @22
    eqid
    #
    drnginvrl
    syl3anc
    @21
    @17
    @4
    @23
    cB
    wcel
    #
    @19
    @25
    @3
    wcel
    @0
    @17
    @4
    @20
    @18
    ad2antrr
    @0
    @4
    @20
    simplr
    @21
    @0
    @26
    @15
    @33
    @27
    @28
    @29
    cB
    cR
    @22
    @14
    c.0
    drngnidl.b
    drngnidl.z
    @32
    drnginvrcl
    syl3anc
    @6
    @19
    @15
    simprl
    cB
    cR
    @24
    cU
    @3
    @23
    @14
    drngnidl.u
    drngnidl.b
    @30
    lidlmcl
    syl22anc
    eqeltrrd
    rexlimdvaa
    imp
    syldan
    @6
    @13
    @8
    wb
    #
    @10
    @0
    @17
    @4
    @34
    @18
    cB
    cR
    cU
    @12
    @3
    drngnidl.u
    drngnidl.b
    @31
    lidl1el
    sylan
    adantr
    mpbid
    olcd
    pm2.61dane
    @3
    @1
    cB
    va
    vex
    elpr
    sylibr
    ex
    ssrdv
    @0
    @17
    @2
    cU
    wss
    #
    @18
    @17
    @1
    cU
    wcel
    #
    cB
    cU
    wcel
    #
    @35
    cR
    cU
    c.0
    drngnidl.u
    drngnidl.z
    lidl0
    cB
    cR
    cU
    drngnidl.u
    drngnidl.b
    lidl1
    @36
    @37
    wa
    @35
    @1
    cB
    cU
    c.0
    snex
    cB
    cR
    cbs
    cfv
    cvv
    drngnidl.b
    cR
    cbs
    fvex
    eqeltri
    prss
    bicomi
    sylanbrc
    syl
    eqssd
end
