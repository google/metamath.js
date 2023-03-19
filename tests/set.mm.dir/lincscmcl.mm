include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wa.mm"
include "clinco.mm"
include "co.mm"
include "cv.mm"
include "csca.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wceq.mm"
include "cmap.mm"
include "wrex.mm"
include "wb.mm"
include "eqid.mm"
include "lcoval.mm"
include "adantr.mm"
include "simpl.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simprl.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "wi.mm"
include "cmulr.mm"
include "cmpt.mm"
include "wf.mm"
include "crg.mm"
include "lmodring.mm"
include "adantl.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl.mm"
include "imp.mm"
include "ringcl.mm"
include "fmptd.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "w3a.mm"
include "3jca.mm"
include "rmfsupp.mm"
include "oveq2.mm"
include "anim12i.mm"
include "lincscm.mm"
include "eqtrd.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimiva.mm"
include "impcom.mm"
include "mpbir2and.mm"
include "sylbid.mm"
include "3impia.mm"

theorem lincscmcl
  let cC: class C
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cM: class M
  let cV: class V
  let vs: setvar s
  let vv: setvar v
  let vx: setvar x
  let vk: setvar k
  assume lincscmcl.s: |- .x. = ( .s ` M )
  assume lincscmcl.r: |- R = ( Base ` ( Scalar ` M ) )


  assert |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) ) /\ C e. R /\ D e. ( M LinCo V ) ) -> ( C .x. D ) e. ( M LinCo V ) )

  proof
    cM
    clmod
    wcel
    #
    cV
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    wa
    #
    cC
    cR
    wcel
    #
    cD
    cM
    cV
    clinco
    co
    #
    wcel
    #
    cC
    cD
    c.x
    co
    #
    @6
    wcel
    #
    @4
    @5
    wa
    #
    @7
    cD
    @1
    wcel
    #
    vx
    cv
    #
    cM
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    cD
    @12
    cV
    cM
    clinc
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vx
    cR
    cV
    cmap
    co
    #
    wrex
    #
    wa
    #
    @9
    @4
    @7
    @22
    wb
    @5
    @1
    cD
    cR
    @13
    cM
    cV
    clmod
    vx
    @1
    eqid
    #
    @13
    eqid
    #
    lincscmcl.r
    lcoval
    adantr
    @10
    @22
    @9
    @10
    @22
    wa
    #
    @9
    @8
    @1
    wcel
    #
    vs
    cv
    #
    @14
    cfsupp
    wbr
    #
    @8
    @27
    cV
    @16
    co
    #
    wceq
    #
    wa
    #
    vs
    @20
    wrex
    #
    @25
    @0
    @5
    @11
    @26
    @4
    @0
    @5
    @22
    @0
    @3
    simpl
    ad2antrr
    @10
    @5
    @22
    @4
    @5
    simpr
    #
    adantr
    @10
    @11
    @21
    simprl
    cC
    c.x
    @13
    cR
    @1
    cM
    cD
    @23
    @24
    lincscmcl.s
    lincscmcl.r
    lmodvscl
    syl3anc
    @22
    @10
    @32
    @21
    @11
    @10
    @32
    wi
    #
    @19
    @11
    @34
    wi
    vx
    @20
    @12
    @20
    wcel
    #
    @19
    wa
    #
    @11
    @34
    @36
    @11
    wa
    #
    @10
    @32
    @37
    @10
    wa
    #
    vv
    cV
    cC
    vv
    cv
    #
    @12
    cfv
    #
    @13
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    @20
    wcel
    #
    @43
    @14
    cfsupp
    wbr
    #
    @8
    @43
    cV
    @16
    co
    #
    wceq
    #
    @32
    @38
    @44
    cV
    cR
    @43
    wf
    #
    @38
    vv
    cV
    @42
    cR
    @43
    @38
    @39
    cV
    wcel
    #
    wa
    @13
    crg
    wcel
    #
    @5
    @40
    cR
    wcel
    #
    @42
    cR
    wcel
    @38
    @50
    @49
    @10
    @50
    @37
    @0
    @50
    @3
    @5
    @13
    cM
    @24
    lmodring
    ad2antrr
    #
    adantl
    adantr
    @38
    @5
    @49
    @10
    @5
    @37
    @33
    adantl
    adantr
    @38
    @49
    @51
    @36
    @49
    @51
    wi
    #
    @11
    @10
    @35
    @53
    @19
    @35
    cV
    cR
    @12
    wf
    #
    @53
    @12
    cR
    cV
    elmapi
    @54
    @49
    @51
    cV
    cR
    @39
    @12
    ffvelrn
    ex
    syl
    adantr
    ad2antrr
    imp
    cR
    @13
    @41
    cC
    @40
    lincscmcl.r
    @41
    eqid
    #
    ringcl
    syl3anc
    @43
    eqid
    #
    fmptd
    @38
    cR
    cvv
    wcel
    @3
    @44
    @48
    wb
    cR
    @13
    cbs
    cfv
    cvv
    lincscmcl.r
    @13
    cbs
    fvex
    eqeltri
    @10
    @3
    @37
    @4
    @3
    @5
    @0
    @3
    simpr
    adantr
    #
    adantl
    cR
    cV
    @43
    cvv
    @2
    elmapg
    sylancr
    mpbird
    @38
    @50
    @3
    @5
    w3a
    #
    @35
    @15
    @45
    @10
    @58
    @37
    @10
    @50
    @3
    @5
    @52
    @57
    @33
    3jca
    adantl
    @36
    @35
    @11
    @10
    @35
    @19
    simpl
    #
    ad2antrr
    @36
    @15
    @11
    @10
    @35
    @15
    @18
    simprl
    ad2antrr
    #
    vv
    @12
    cC
    cR
    @13
    cV
    @2
    lincscmcl.r
    rmfsupp
    syl3anc
    @38
    @8
    cC
    @17
    c.x
    co
    #
    @46
    @36
    @8
    @61
    wceq
    #
    @11
    @10
    @19
    @62
    @35
    @18
    @62
    @15
    cD
    @17
    cC
    c.x
    oveq2
    adantl
    adantl
    ad2antrr
    @38
    @4
    @35
    @5
    wa
    @15
    @61
    @46
    wceq
    @37
    @4
    @5
    simprl
    @37
    @35
    @10
    @5
    @36
    @35
    @11
    @59
    adantr
    @33
    anim12i
    @60
    vv
    @12
    cR
    cC
    c.x
    @41
    @43
    cM
    cV
    @17
    lincscmcl.s
    @55
    @17
    eqid
    lincscmcl.r
    @56
    lincscm
    syl3anc
    eqtrd
    @31
    @45
    @47
    wa
    vs
    @43
    @20
    @27
    @43
    wceq
    #
    @28
    @45
    @30
    @47
    @27
    @43
    @14
    cfsupp
    breq1
    @63
    @29
    @46
    @8
    @27
    @43
    cV
    @16
    oveq1
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    ex
    ex
    rexlimiva
    impcom
    impcom
    @4
    @9
    @26
    @32
    wa
    wb
    @5
    @22
    @1
    @8
    cR
    @13
    cM
    cV
    clmod
    vs
    @23
    @24
    lincscmcl.r
    lcoval
    ad2antrr
    mpbir2and
    ex
    sylbid
    3impia
end
