include "ccrg.mm"
include "wcel.mm"
include "clmhm.mm"
include "co.mm"
include "w3a.mm"
include "cvsca.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "clmod.mm"
include "lmhmlmod1.mm"
include "3ad2ant3.mm"
include "lmhmlmod2.mm"
include "wceq.mm"
include "lmhmsca.mm"
include "cv.mm"
include "cmpt.mm"
include "ccom.mm"
include "cghm.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "simpl2.mm"
include "wf.mm"
include "lmhmf.mm"
include "ffvelrnda.mm"
include "fconstmpt.mm"
include "feqmptd.mm"
include "offval2.mm"
include "eqidd.mm"
include "oveq2.mm"
include "fmptco.mm"
include "eqtr4d.mm"
include "simp2.mm"
include "lmodvsghm.mm"
include "syl2anc.mm"
include "lmghm.mm"
include "ghmco.mm"
include "eqeltrd.mm"
include "wa.mm"
include "cmulr.mm"
include "simpl1.mm"
include "simprl.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "crngcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"
include "lmodvscl.mm"
include "3expb.mm"
include "sylan.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "lmhmlin.mm"
include "3ad2antl3.mm"
include "ofc1.mm"
include "mpdan.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "islmhmd.mm"

theorem lmhmvsca
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume lmhmvsca.v: |- V = ( Base ` M )
  assume lmhmvsca.s: |- .x. = ( .s ` N )
  assume lmhmvsca.j: |- J = ( Scalar ` N )
  assume lmhmvsca.k: |- K = ( Base ` J )


  assert |- ( ( J e. CRing /\ A e. K /\ F e. ( M LMHom N ) ) -> ( ( V X. { A } ) oF .x. F ) e. ( M LMHom N ) )

  proof
    cJ
    ccrg
    wcel
    #
    cA
    cK
    wcel
    #
    cF
    cM
    cN
    clmhm
    co
    wcel
    #
    w3a
    #
    vx
    vy
    cM
    cN
    cM
    cvsca
    cfv
    #
    c.x
    cV
    cA
    csn
    cxp
    #
    cF
    c.x
    cof
    co
    #
    cJ
    cM
    csca
    cfv
    #
    @7
    cbs
    cfv
    #
    cV
    lmhmvsca.v
    @4
    eqid
    #
    lmhmvsca.s
    @7
    eqid
    #
    lmhmvsca.j
    @8
    eqid
    #
    @2
    @0
    cM
    clmod
    wcel
    #
    @1
    cM
    cN
    cF
    lmhmlmod1
    3ad2ant3
    #
    @2
    @0
    cN
    clmod
    wcel
    #
    @1
    cM
    cN
    cF
    lmhmlmod2
    3ad2ant3
    #
    @2
    @0
    cJ
    @7
    wceq
    @1
    cM
    cN
    cF
    @7
    cJ
    @10
    lmhmvsca.j
    lmhmsca
    3ad2ant3
    #
    @3
    @6
    vu
    cN
    cbs
    cfv
    #
    cA
    vu
    cv
    #
    c.x
    co
    #
    cmpt
    #
    cF
    ccom
    #
    cM
    cN
    cghm
    co
    #
    @3
    @6
    vv
    cV
    cA
    vv
    cv
    #
    cF
    cfv
    #
    c.x
    co
    #
    cmpt
    @21
    @3
    vv
    cV
    cA
    @24
    c.x
    @5
    cF
    cvv
    cK
    @17
    cV
    cvv
    wcel
    #
    @3
    cV
    cM
    cbs
    cfv
    cvv
    lmhmvsca.v
    cM
    cbs
    fvex
    eqeltri
    #
    a1i
    @0
    @1
    @2
    @23
    cV
    wcel
    simpl2
    @3
    cV
    @17
    @23
    cF
    @2
    @0
    cV
    @17
    cF
    wf
    #
    @1
    cV
    @17
    cM
    cN
    cF
    lmhmvsca.v
    @17
    eqid
    #
    lmhmf
    3ad2ant3
    #
    ffvelrnda
    #
    @5
    vv
    cV
    cA
    cmpt
    wceq
    @3
    vv
    cV
    cA
    fconstmpt
    a1i
    @3
    vv
    cV
    @17
    cF
    @30
    feqmptd
    #
    offval2
    @3
    vv
    vu
    cV
    @17
    @24
    @19
    @25
    cF
    @20
    @31
    @32
    @3
    @20
    eqidd
    @18
    @24
    cA
    c.x
    oveq2
    fmptco
    eqtr4d
    @3
    @20
    cN
    cN
    cghm
    co
    wcel
    #
    cF
    @22
    wcel
    #
    @21
    @22
    wcel
    @3
    @14
    @1
    @33
    @15
    @0
    @1
    @2
    simp2
    vu
    cA
    c.x
    cJ
    cK
    @17
    cN
    @29
    lmhmvsca.j
    lmhmvsca.s
    lmhmvsca.k
    lmodvsghm
    syl2anc
    @2
    @0
    @34
    @1
    cM
    cN
    cF
    lmghm
    3ad2ant3
    cM
    cN
    cN
    @20
    cF
    ghmco
    syl2anc
    eqeltrd
    @3
    vx
    cv
    #
    @8
    wcel
    #
    vy
    cv
    #
    cV
    wcel
    #
    wa
    #
    wa
    #
    cA
    @35
    @37
    cF
    cfv
    #
    c.x
    co
    #
    c.x
    co
    #
    @35
    cA
    @41
    c.x
    co
    #
    c.x
    co
    #
    @35
    @37
    @4
    co
    #
    @6
    cfv
    #
    @35
    @37
    @6
    cfv
    #
    c.x
    co
    @40
    cA
    @35
    cJ
    cmulr
    cfv
    #
    co
    #
    @41
    c.x
    co
    #
    @35
    cA
    @49
    co
    #
    @41
    c.x
    co
    #
    @43
    @45
    @40
    @50
    @52
    @41
    c.x
    @40
    @0
    @1
    @35
    cK
    wcel
    #
    @50
    @52
    wceq
    @0
    @1
    @2
    @39
    simpl1
    @0
    @1
    @2
    @39
    simpl2
    #
    @40
    @35
    @8
    cK
    @3
    @36
    @38
    simprl
    @3
    cK
    @8
    wceq
    @39
    @3
    cK
    cJ
    cbs
    cfv
    @8
    lmhmvsca.k
    @3
    cJ
    @7
    cbs
    @16
    fveq2d
    syl5eq
    adantr
    eleqtrrd
    #
    cK
    cJ
    @49
    cA
    @35
    lmhmvsca.k
    @49
    eqid
    #
    crngcom
    syl3anc
    oveq1d
    @40
    @14
    @1
    @54
    @41
    @17
    wcel
    #
    @51
    @43
    wceq
    @3
    @14
    @39
    @15
    adantr
    #
    @55
    @56
    @40
    cV
    @17
    @37
    cF
    @3
    @28
    @39
    @30
    adantr
    @3
    @36
    @38
    simprr
    #
    ffvelrnd
    #
    cA
    @35
    c.x
    @49
    cJ
    cK
    @17
    cN
    @41
    @29
    lmhmvsca.j
    lmhmvsca.s
    lmhmvsca.k
    @57
    lmodvsass
    syl13anc
    @40
    @14
    @54
    @1
    @58
    @53
    @45
    wceq
    @59
    @56
    @55
    @61
    @35
    cA
    c.x
    @49
    cJ
    cK
    @17
    cN
    @41
    @29
    lmhmvsca.j
    lmhmvsca.s
    lmhmvsca.k
    @57
    lmodvsass
    syl13anc
    3eqtr3d
    @40
    @46
    cV
    wcel
    #
    @47
    @43
    wceq
    @3
    @12
    @39
    @62
    @13
    @12
    @36
    @38
    @62
    @35
    @4
    @7
    @8
    cV
    cM
    @37
    lmhmvsca.v
    @10
    @9
    @11
    lmodvscl
    3expb
    sylan
    @40
    cV
    cA
    @42
    c.x
    cF
    cvv
    cK
    @46
    @26
    @40
    @27
    a1i
    #
    @55
    @3
    cF
    cV
    wfn
    #
    @39
    @3
    @28
    @64
    @30
    cV
    @17
    cF
    ffn
    syl
    adantr
    #
    @40
    @46
    cF
    cfv
    @42
    wceq
    #
    @62
    @2
    @0
    @39
    @66
    @1
    @2
    @36
    @38
    @66
    @8
    cM
    cN
    @4
    c.x
    cV
    cF
    @7
    @35
    @37
    @10
    @11
    lmhmvsca.v
    @9
    lmhmvsca.s
    lmhmlin
    3expb
    3ad2antl3
    adantr
    ofc1
    mpdan
    @40
    @48
    @44
    @35
    c.x
    @40
    @38
    @48
    @44
    wceq
    @60
    @40
    cV
    cA
    @41
    c.x
    cF
    cvv
    cK
    @37
    @63
    @55
    @65
    @40
    @38
    wa
    @41
    eqidd
    ofc1
    mpdan
    oveq2d
    3eqtr4d
    islmhmd
end
