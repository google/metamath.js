include "ctmd.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cfv.mm"
include "wa.mm"
include "cmnd.mm"
include "ctps.mm"
include "cplusf.mm"
include "ctopn.mm"
include "crest.mm"
include "co.mm"
include "ctx.mm"
include "ccn.mm"
include "submmnd.mm"
include "adantl.mm"
include "cress.mm"
include "tmdtps.mm"
include "resstps.mm"
include "sylan.mm"
include "syl5eqel.mm"
include "cv.mm"
include "cplusg.mm"
include "cmpt2.mm"
include "cbs.mm"
include "wceq.mm"
include "submbas.mm"
include "eqid.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "mpt2eq123dv.mm"
include "plusffval.mm"
include "syl6reqr.mm"
include "ctopon.mm"
include "tmdtopon.mm"
include "adantr.mm"
include "wss.mm"
include "submss.mm"
include "tmdcn.mm"
include "syl5eqelr.mm"
include "cnmpt2res.mm"
include "eqeltrd.mm"
include "crn.mm"
include "wb.mm"
include "cxp.mm"
include "wf.mm"
include "mndplusf.mm"
include "frn.mm"
include "3syl.mm"
include "sseqtr4d.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "resstopn.mm"
include "istmd.mm"
include "syl3anbrc.mm"

theorem submtmd
  let cS: class S
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume subgtgp.h: |- H = ( G |`s S )


  assert |- ( ( G e. TopMnd /\ S e. ( SubMnd ` G ) ) -> H e. TopMnd )

  proof
    cG
    ctmd
    wcel
    #
    cS
    cG
    csubmnd
    cfv
    #
    wcel
    #
    wa
    #
    cH
    cmnd
    wcel
    #
    cH
    ctps
    wcel
    cH
    cplusf
    cfv
    #
    cG
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    @7
    ctx
    co
    #
    @7
    ccn
    co
    wcel
    #
    cH
    ctmd
    wcel
    @2
    @4
    @0
    cS
    cH
    cG
    subgtgp.h
    submmnd
    adantl
    #
    @3
    cH
    cG
    cS
    cress
    co
    #
    ctps
    subgtgp.h
    @0
    cG
    ctps
    wcel
    @2
    @11
    ctps
    wcel
    cG
    tmdtps
    cS
    cG
    @1
    resstps
    sylan
    syl5eqel
    @3
    @5
    @8
    @6
    ccn
    co
    #
    wcel
    #
    @9
    @3
    @5
    vx
    vy
    cS
    cS
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    @12
    @3
    @18
    vx
    vy
    cH
    cbs
    cfv
    #
    @19
    @14
    @15
    cH
    cplusg
    cfv
    #
    co
    #
    cmpt2
    @5
    @3
    vx
    vy
    cS
    cS
    @17
    @19
    @19
    @21
    @2
    cS
    @19
    wceq
    @0
    cS
    cH
    cG
    subgtgp.h
    submbas
    adantl
    #
    @22
    @3
    @16
    @20
    @14
    @15
    @2
    @16
    @20
    wceq
    @0
    cS
    @16
    cG
    cH
    @1
    subgtgp.h
    @16
    eqid
    #
    ressplusg
    adantl
    oveqd
    mpt2eq123dv
    vx
    vy
    @19
    @20
    @5
    cH
    @19
    eqid
    #
    @20
    eqid
    @5
    eqid
    #
    plusffval
    syl6reqr
    @3
    vx
    vy
    @17
    @6
    @7
    @6
    @6
    @7
    cS
    cG
    cbs
    cfv
    #
    cS
    @26
    @7
    eqid
    #
    @0
    @6
    @26
    ctopon
    cfv
    wcel
    #
    @2
    cG
    @6
    @26
    @6
    eqid
    #
    @26
    eqid
    #
    tmdtopon
    adantr
    #
    @2
    cS
    @26
    wss
    #
    @0
    @26
    cS
    cG
    @30
    submss
    adantl
    #
    @27
    @31
    @33
    @0
    vx
    vy
    @26
    @26
    @17
    cmpt2
    #
    @6
    @6
    ctx
    co
    @6
    ccn
    co
    #
    wcel
    @2
    @0
    @34
    cG
    cplusf
    cfv
    #
    @35
    vx
    vy
    @26
    @16
    @36
    cG
    @30
    @23
    @36
    eqid
    #
    plusffval
    @36
    cG
    @6
    @29
    @37
    tmdcn
    syl5eqelr
    adantr
    cnmpt2res
    eqeltrd
    @3
    @28
    @5
    crn
    #
    cS
    wss
    @32
    @13
    @9
    wb
    @31
    @3
    @38
    @19
    cS
    @3
    @4
    @19
    @19
    cxp
    #
    @19
    @5
    wf
    @38
    @19
    wss
    @10
    @19
    @5
    cH
    @24
    @25
    mndplusf
    @39
    @19
    @5
    frn
    3syl
    @22
    sseqtr4d
    @33
    cS
    @5
    @8
    @6
    @26
    cnrest2
    syl3anc
    mpbid
    @5
    cH
    @7
    @25
    cS
    cH
    @6
    cG
    subgtgp.h
    @29
    resstopn
    istmd
    syl3anbrc
end
