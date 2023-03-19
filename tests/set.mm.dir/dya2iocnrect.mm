include "cr.mm"
include "cxp.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "cioo.mm"
include "crn.mm"
include "wrex.mm"
include "wa.mm"
include "wss.mm"
include "cmpt2.mm"
include "eleq2i.mm"
include "eqid.mm"
include "vex.mm"
include "xpex.mm"
include "elrnmpt2.mm"
include "sylbb.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "simp3.mm"
include "jca32.mm"
include "r19.41vv.mm"
include "biimpri.mm"
include "simprl.mm"
include "simpl.mm"
include "simprr.mm"
include "eleqtrd.mm"
include "3jca.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "simpr.mm"
include "xp1st.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "simpll.mm"
include "3ad2ant3.mm"
include "dya2icoseg2.mm"
include "syl3anc.mm"
include "xp2nd.mm"
include "simplr.mm"
include "reeanv.mm"
include "sylanbrc.mm"
include "xpeq1.mm"
include "eqeq2d.mm"
include "xpeq2.mm"
include "rspc2ev.mm"
include "mp3an3.mm"
include "sylibr.mm"
include "ad2antrl.mm"
include "cvv.mm"
include "xpss.mm"
include "simpl1.mm"
include "sseldi.mm"
include "simprrl.mm"
include "simpld.mm"
include "simprrr.mm"
include "elxp7.mm"
include "syl12anc.mm"
include "simprd.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "simpl2.mm"
include "sseqtr4d.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "exp32.mm"
include "rexlimdvv.mm"
include "sylc.mm"
include "sylan2.mm"
include "ex.mm"
include "rexlimivv.mm"
include "3syl.mm"

theorem dya2iocnrect
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cR: class R
  let ve: setvar e
  let vf: setvar f
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let cX: class X
  let vb: setvar b
  let vs: setvar s
  let vt: setvar t
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )
  assume dya2ioc.2: |- R = ( u e. ran I , v e. ran I |-> ( u X. v ) )
  assume dya2iocnrect.1: |- B = ran ( e e. ran (,) , f e. ran (,) |-> ( e X. f ) )

  disjoint n x
  disjoint b e
  disjoint b f
  disjoint A b
  disjoint e f
  disjoint A e
  disjoint A f
  disjoint u v
  disjoint u x
  disjoint I u
  disjoint v x
  disjoint I v
  disjoint I x
  disjoint R b
  disjoint R e
  disjoint R f
  disjoint b x
  disjoint X b
  disjoint e x
  disjoint X e
  disjoint f x
  disjoint X f
  disjoint X x
  disjoint n x
  disjoint I x
  disjoint u v
  disjoint I u
  disjoint I v
  disjoint u x
  disjoint v x
  disjoint n s
  disjoint n t
  disjoint s t
  disjoint s x
  disjoint t x
  disjoint b s
  disjoint b t
  disjoint e s
  disjoint e t
  disjoint f s
  disjoint f t
  disjoint A s
  disjoint A t
  disjoint s u
  disjoint s v
  disjoint I s
  disjoint t u
  disjoint t v
  disjoint I t
  disjoint R s
  disjoint R t
  disjoint X s
  disjoint X t
  assert |- ( ( X e. ( RR X. RR ) /\ A e. B /\ X e. A ) -> E. b e. ran R ( X e. b /\ b C_ A ) )

  proof
    cX
    cr
    cr
    cxp
    #
    wcel
    #
    cA
    cB
    wcel
    #
    cX
    cA
    wcel
    #
    w3a
    #
    cA
    ve
    cv
    #
    vf
    cv
    #
    cxp
    #
    wceq
    #
    vf
    cioo
    crn
    #
    wrex
    ve
    @9
    wrex
    #
    @1
    @3
    wa
    #
    wa
    #
    @8
    @11
    wa
    #
    vf
    @9
    wrex
    ve
    @9
    wrex
    #
    cX
    vb
    cv
    #
    wcel
    #
    @15
    cA
    wss
    #
    wa
    #
    vb
    cR
    crn
    #
    wrex
    #
    @4
    @10
    @1
    @3
    @2
    @1
    @10
    @3
    @2
    cA
    ve
    vf
    @9
    @9
    @7
    cmpt2
    #
    crn
    #
    wcel
    @10
    cB
    @22
    cA
    dya2iocnrect.1
    eleq2i
    ve
    vf
    @9
    @9
    @7
    cA
    @21
    @21
    eqid
    @5
    @6
    ve
    vex
    vf
    vex
    xpex
    elrnmpt2
    sylbb
    3ad2ant2
    @1
    @2
    @3
    simp1
    @1
    @2
    @3
    simp3
    jca32
    @14
    @12
    @8
    @11
    ve
    vf
    @9
    @9
    r19.41vv
    biimpri
    @13
    @20
    ve
    vf
    @9
    @9
    @5
    @9
    wcel
    #
    @6
    @9
    wcel
    #
    wa
    #
    @13
    @20
    @13
    @25
    @1
    @8
    cX
    @7
    wcel
    #
    w3a
    #
    @20
    @13
    @1
    @8
    @26
    @8
    @1
    @3
    simprl
    @8
    @11
    simpl
    #
    @13
    cX
    cA
    @7
    @8
    @1
    @3
    simprr
    @28
    eleqtrd
    3jca
    @25
    @27
    wa
    #
    @27
    cX
    c1st
    cfv
    #
    vs
    cv
    #
    wcel
    #
    @31
    @5
    wss
    #
    wa
    #
    cX
    c2nd
    cfv
    #
    vt
    cv
    #
    wcel
    #
    @36
    @6
    wss
    #
    wa
    #
    wa
    #
    vt
    cI
    crn
    #
    wrex
    vs
    @41
    wrex
    #
    @20
    @25
    @27
    simpr
    @29
    @34
    vs
    @41
    wrex
    #
    @39
    vt
    @41
    wrex
    #
    @42
    @29
    @30
    cr
    wcel
    #
    @23
    @30
    @5
    wcel
    #
    @43
    @27
    @45
    @25
    @1
    @8
    @45
    @26
    cX
    cr
    cr
    xp1st
    3ad2ant1
    adantl
    @23
    @24
    @27
    simpll
    @27
    @46
    @25
    @26
    @1
    @46
    @8
    cX
    @5
    @6
    xp1st
    3ad2ant3
    adantl
    vx
    vn
    @5
    cI
    cJ
    @30
    vs
    sxbrsiga.0
    dya2ioc.1
    dya2icoseg2
    syl3anc
    @29
    @35
    cr
    wcel
    #
    @24
    @35
    @6
    wcel
    #
    @44
    @27
    @47
    @25
    @1
    @8
    @47
    @26
    cX
    cr
    cr
    xp2nd
    3ad2ant1
    adantl
    @23
    @24
    @27
    simplr
    @27
    @48
    @25
    @26
    @1
    @48
    @8
    cX
    @5
    @6
    xp2nd
    3ad2ant3
    adantl
    vx
    vn
    @6
    cI
    cJ
    @35
    vt
    sxbrsiga.0
    dya2ioc.1
    dya2icoseg2
    syl3anc
    @34
    @39
    vs
    vt
    @41
    @41
    reeanv
    sylanbrc
    @27
    @40
    @20
    vs
    vt
    @41
    @41
    @27
    @31
    @41
    wcel
    #
    @36
    @41
    wcel
    #
    wa
    #
    @40
    @20
    @27
    @51
    @40
    wa
    #
    wa
    #
    @31
    @36
    cxp
    #
    @19
    wcel
    #
    cX
    @54
    wcel
    #
    @54
    cA
    wss
    #
    @20
    @51
    @55
    @27
    @40
    @51
    @54
    vu
    cv
    #
    vv
    cv
    #
    cxp
    #
    wceq
    #
    vv
    @41
    wrex
    vu
    @41
    wrex
    #
    @55
    @49
    @50
    @54
    @54
    wceq
    #
    @62
    @54
    eqid
    @61
    @63
    @54
    @31
    @59
    cxp
    #
    wceq
    vu
    vv
    @31
    @36
    @41
    @41
    @58
    @31
    wceq
    @60
    @64
    @54
    @58
    @31
    @59
    xpeq1
    eqeq2d
    @59
    @36
    wceq
    @64
    @54
    @54
    @59
    @36
    @31
    xpeq2
    eqeq2d
    rspc2ev
    mp3an3
    vu
    vv
    @41
    @41
    @60
    @54
    cR
    dya2ioc.2
    @58
    @59
    vu
    vex
    vv
    vex
    xpex
    elrnmpt2
    sylibr
    ad2antrl
    @53
    cX
    cvv
    cvv
    cxp
    #
    wcel
    #
    @32
    @37
    @56
    @53
    @0
    @65
    cX
    cr
    cr
    xpss
    @1
    @8
    @26
    @52
    simpl1
    sseldi
    @53
    @32
    @33
    @27
    @51
    @34
    @39
    simprrl
    #
    simpld
    @53
    @37
    @38
    @27
    @51
    @34
    @39
    simprrr
    #
    simpld
    @56
    @66
    @32
    @37
    wa
    wa
    cX
    @31
    @36
    elxp7
    biimpri
    syl12anc
    @53
    @54
    @7
    cA
    @53
    @33
    @38
    @54
    @7
    wss
    @53
    @32
    @33
    @67
    simprd
    @53
    @37
    @38
    @68
    simprd
    @31
    @5
    @36
    @6
    xpss12
    syl2anc
    @1
    @8
    @26
    @52
    simpl2
    sseqtr4d
    @18
    @56
    @57
    wa
    vb
    @54
    @19
    @15
    @54
    wceq
    @16
    @56
    @17
    @57
    @15
    @54
    cX
    eleq2
    @15
    @54
    cA
    sseq1
    anbi12d
    rspcev
    syl12anc
    exp32
    rexlimdvv
    sylc
    sylan2
    ex
    rexlimivv
    3syl
end
