include "ctgp.mm"
include "wcel.mm"
include "cgrp.mm"
include "ctps.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "w3a.mm"
include "tgpgrp.mm"
include "tgptps.mm"
include "tgpsubcn.mm"
include "3jca.mm"
include "ctmd.mm"
include "cminusg.mm"
include "cfv.mm"
include "simp1.mm"
include "cmnd.mm"
include "cplusf.mm"
include "grpmnd.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "cbs.mm"
include "cv.mm"
include "cmpt2.mm"
include "cplusg.mm"
include "eqid.mm"
include "simp3.mm"
include "grpsubinv.mm"
include "mpt2eq3dva.mm"
include "plusffval.mm"
include "syl6eqr.mm"
include "ctopon.mm"
include "istps.mm"
include "sylib.mm"
include "cnmpt1st.mm"
include "cnmpt2nd.mm"
include "c0g.mm"
include "cmpt.mm"
include "wf.mm"
include "grpinvf.mm"
include "feqmptd.mm"
include "wceq.mm"
include "grpinvval2.mm"
include "sylan.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "grpidcl.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "cnmpt12f.mm"
include "eqeltrd.mm"
include "cnmpt21f.mm"
include "cnmpt22f.mm"
include "eqeltrrd.mm"
include "istmd.mm"
include "syl3anbrc.mm"
include "istgp.mm"
include "impbii.mm"

theorem istgp2
  let cG: class G
  let cJ: class J
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  assume tgpsubcn.2: |- J = ( TopOpen ` G )
  assume tgpsubcn.3: |- .- = ( -g ` G )


  assert |- ( G e. TopGrp <-> ( G e. Grp /\ G e. TopSp /\ .- e. ( ( J tX J ) Cn J ) ) )

  proof
    cG
    ctgp
    wcel
    #
    cG
    cgrp
    wcel
    #
    cG
    ctps
    wcel
    #
    c.mi
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    #
    wcel
    #
    w3a
    #
    @0
    @1
    @2
    @4
    cG
    tgpgrp
    cG
    tgptps
    cG
    cJ
    c.mi
    tgpsubcn.2
    tgpsubcn.3
    tgpsubcn
    3jca
    @5
    @1
    cG
    ctmd
    wcel
    #
    cG
    cminusg
    cfv
    #
    cJ
    cJ
    ccn
    co
    #
    wcel
    @0
    @1
    @2
    @4
    simp1
    #
    @5
    cG
    cmnd
    wcel
    #
    @2
    cG
    cplusf
    cfv
    #
    @3
    wcel
    @6
    @1
    @2
    @10
    @4
    cG
    grpmnd
    3ad2ant1
    @1
    @2
    @4
    simp2
    #
    @5
    vx
    vy
    cG
    cbs
    cfv
    #
    @13
    vx
    cv
    #
    vy
    cv
    #
    @7
    cfv
    #
    c.mi
    co
    #
    cmpt2
    #
    @11
    @3
    @5
    @18
    vx
    vy
    @13
    @13
    @14
    @15
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt2
    @11
    @5
    vx
    vy
    @13
    @13
    @17
    @20
    @5
    @14
    @13
    wcel
    #
    @15
    @13
    wcel
    #
    w3a
    @13
    @19
    cG
    c.mi
    @7
    @14
    @15
    @13
    eqid
    #
    @19
    eqid
    #
    tgpsubcn.3
    @7
    eqid
    #
    @5
    @21
    @1
    @22
    @9
    3ad2ant1
    @5
    @21
    @22
    simp2
    @5
    @21
    @22
    simp3
    grpsubinv
    mpt2eq3dva
    vx
    vy
    @13
    @19
    @11
    cG
    @23
    @24
    @11
    eqid
    #
    plusffval
    syl6eqr
    @5
    vx
    vy
    @14
    @16
    c.mi
    cJ
    cJ
    cJ
    cJ
    cJ
    @13
    @13
    @5
    @2
    cJ
    @13
    ctopon
    cfv
    wcel
    @12
    @13
    cJ
    cG
    @23
    tgpsubcn.2
    istps
    sylib
    #
    @27
    @5
    vx
    vy
    cJ
    cJ
    @13
    @13
    @27
    @27
    cnmpt1st
    @5
    vx
    vy
    @15
    @7
    cJ
    cJ
    cJ
    cJ
    @13
    @13
    @27
    @27
    @5
    vx
    vy
    cJ
    cJ
    @13
    @13
    @27
    @27
    cnmpt2nd
    @5
    @7
    vx
    @13
    cG
    c0g
    cfv
    #
    @14
    c.mi
    co
    #
    cmpt
    #
    @8
    @5
    @7
    vx
    @13
    @14
    @7
    cfv
    #
    cmpt
    @30
    @5
    vx
    @13
    @13
    @7
    @1
    @2
    @13
    @13
    @7
    wf
    @4
    @13
    cG
    @7
    @23
    @25
    grpinvf
    3ad2ant1
    feqmptd
    @5
    vx
    @13
    @31
    @29
    @5
    @1
    @21
    @31
    @29
    wceq
    @9
    @13
    cG
    c.mi
    @7
    @14
    @28
    @23
    tgpsubcn.3
    @25
    @28
    eqid
    #
    grpinvval2
    sylan
    mpteq2dva
    eqtrd
    @5
    vx
    @28
    @14
    c.mi
    cJ
    cJ
    cJ
    cJ
    @13
    @27
    @5
    vx
    @28
    cJ
    cJ
    @13
    @13
    @27
    @27
    @1
    @2
    @28
    @13
    wcel
    @4
    @13
    cG
    @28
    @23
    @32
    grpidcl
    3ad2ant1
    cnmptc
    @5
    vx
    cJ
    @13
    @27
    cnmptid
    @1
    @2
    @4
    simp3
    #
    cnmpt12f
    eqeltrd
    #
    cnmpt21f
    @33
    cnmpt22f
    eqeltrrd
    @11
    cG
    cJ
    @26
    tgpsubcn.2
    istmd
    syl3anbrc
    @34
    cG
    @7
    cJ
    tgpsubcn.2
    @25
    istgp
    syl3anbrc
    impbii
end
