include "ccph.mm"
include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "cocv.mm"
include "cfv.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "csca.mm"
include "c0g.mm"
include "wceq.mm"
include "cbs.mm"
include "crab.mm"
include "ciin.mm"
include "cin.mm"
include "ccld.mm"
include "eqid.mm"
include "cssi.mm"
include "adantl.mm"
include "wral.mm"
include "wss.mm"
include "ocvss.mm"
include "ocvval.mm"
include "mp1i.mm"
include "riinrab.mm"
include "syl6eqr.mm"
include "ctopon.mm"
include "ctps.mm"
include "cnlm.mm"
include "cngp.mm"
include "cphnlm.mm"
include "adantr.mm"
include "nlmngp.mm"
include "ngptps.mm"
include "3syl.mm"
include "istps.mm"
include "sylib.mm"
include "toponuni.mm"
include "syl.mm"
include "ineq1d.mm"
include "3eqtrd.mm"
include "ctop.mm"
include "topontop.mm"
include "sseli.mm"
include "cmpt.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cvv.mm"
include "fvex.mm"
include "mptiniseg.mm"
include "ax-mp.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "ccn.mm"
include "simpll.mm"
include "cnmptid.mm"
include "simpr.mm"
include "cnmptc.mm"
include "cnmpt1ip.mm"
include "cha.mm"
include "cc.mm"
include "cnfldhaus.mm"
include "cc0.mm"
include "cclm.mm"
include "cphclm.mm"
include "clm0.mm"
include "ad2antrr.mm"
include "0cn.mm"
include "syl6eqelr.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "sncld.mm"
include "sylancr.mm"
include "cnclima.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "riincld.mm"
include "eqeltrd.mm"

theorem csscld
  let cC: class C
  let cS: class S
  let cJ: class J
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume csscld.c: |- C = ( CSubSp ` W )
  assume csscld.j: |- J = ( TopOpen ` W )


  assert |- ( ( W e. CPreHil /\ S e. C ) -> S e. ( Clsd ` J ) )

  proof
    cW
    ccph
    wcel
    #
    cS
    cC
    wcel
    #
    wa
    #
    cS
    cJ
    cuni
    #
    vy
    cS
    cW
    cocv
    cfv
    #
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    cW
    cip
    cfv
    #
    co
    #
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    vx
    cW
    cbs
    cfv
    #
    crab
    #
    ciin
    #
    cin
    #
    cJ
    ccld
    cfv
    #
    @2
    cS
    @5
    @4
    cfv
    #
    @13
    @15
    cin
    #
    @16
    @1
    cS
    @18
    wceq
    @0
    cC
    cS
    @4
    cW
    @4
    eqid
    #
    csscld.c
    cssi
    adantl
    @2
    @18
    @12
    vy
    @5
    wral
    vx
    @13
    crab
    #
    @19
    @5
    @13
    wss
    @18
    @21
    wceq
    @2
    cS
    @4
    @13
    cW
    @13
    eqid
    #
    @20
    ocvss
    #
    vx
    vy
    @5
    @10
    @8
    @4
    @13
    cW
    @11
    @22
    @8
    eqid
    #
    @10
    eqid
    #
    @11
    eqid
    @20
    ocvval
    mp1i
    @12
    vy
    vx
    @13
    @5
    riinrab
    syl6eqr
    @2
    @13
    @3
    @15
    @2
    cJ
    @13
    ctopon
    cfv
    wcel
    #
    @13
    @3
    wceq
    @2
    cW
    ctps
    wcel
    #
    @26
    @2
    cW
    cnlm
    wcel
    #
    cW
    cngp
    wcel
    @27
    @0
    @28
    @1
    cW
    cphnlm
    adantr
    cW
    nlmngp
    cW
    ngptps
    3syl
    @13
    cJ
    cW
    @22
    csscld.j
    istps
    sylib
    #
    @13
    cJ
    toponuni
    syl
    ineq1d
    3eqtrd
    @2
    cJ
    ctop
    wcel
    #
    @14
    @17
    wcel
    #
    vy
    @5
    wral
    @16
    @17
    wcel
    @2
    @26
    @30
    @29
    @13
    cJ
    topontop
    syl
    @2
    @31
    vy
    @5
    @7
    @5
    wcel
    @2
    @7
    @13
    wcel
    #
    @31
    @5
    @13
    @7
    @23
    sseli
    @2
    @32
    wa
    #
    @14
    vx
    @13
    @9
    cmpt
    #
    ccnv
    @11
    csn
    #
    cima
    #
    @17
    @11
    cvv
    wcel
    @36
    @14
    wceq
    @10
    c0g
    fvex
    vx
    @13
    @9
    @11
    @34
    cvv
    @34
    eqid
    mptiniseg
    ax-mp
    @33
    @34
    cJ
    ccnfld
    ctopn
    cfv
    #
    ccn
    co
    wcel
    @35
    @37
    ccld
    cfv
    wcel
    #
    @36
    @17
    wcel
    @33
    vx
    @6
    @7
    @37
    @8
    cJ
    cJ
    cW
    @13
    csscld.j
    @37
    eqid
    #
    @24
    @0
    @1
    @32
    simpll
    @2
    @26
    @32
    @29
    adantr
    #
    @33
    vx
    cJ
    @13
    @40
    cnmptid
    @33
    vx
    @7
    cJ
    cJ
    @13
    @13
    @40
    @40
    @2
    @32
    simpr
    cnmptc
    cnmpt1ip
    @33
    @37
    cha
    wcel
    @11
    cc
    wcel
    @38
    @37
    @39
    cnfldhaus
    @33
    @11
    cc0
    cc
    @0
    cc0
    @11
    wceq
    #
    @1
    @32
    @0
    cW
    cclm
    wcel
    @41
    cW
    cphclm
    @10
    cW
    @25
    clm0
    syl
    ad2antrr
    0cn
    syl6eqelr
    @11
    @37
    cc
    cc
    @37
    @37
    @39
    cnfldtopon
    toponunii
    sncld
    sylancr
    @35
    @34
    cJ
    @37
    cnclima
    syl2anc
    syl5eqelr
    sylan2
    ralrimiva
    vy
    @5
    @14
    cJ
    @3
    @3
    eqid
    riincld
    syl2anc
    eqeltrd
end
