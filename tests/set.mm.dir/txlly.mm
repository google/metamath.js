include "clly.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "ctop.mm"
include "cv.mm"
include "crest.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "llytop.mm"
include "txtop.mm"
include "syl2an.mm"
include "cxp.mm"
include "wss.mm"
include "eltx.mm"
include "c1st.mm"
include "cfv.mm"
include "w3a.mm"
include "c2nd.mm"
include "simpll.mm"
include "simprll.mm"
include "simprrl.mm"
include "xp1st.mm"
include "syl.mm"
include "llyi.mm"
include "syl3anc.mm"
include "simplr.mm"
include "simprlr.mm"
include "xp2nd.mm"
include "reeanv.mm"
include "ad3antrrr.mm"
include "ad3antlr.mm"
include "txopn.mm"
include "syl22anc.mm"
include "simprl1.mm"
include "simprr1.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "simprrr.mm"
include "sylan9ssr.mm"
include "vex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "elind.mm"
include "cop.mm"
include "wceq.mm"
include "1st2nd2.mm"
include "adantr.mm"
include "simprl2.mm"
include "simprr2.mm"
include "opelxpi.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "txrest.mm"
include "simprl3.mm"
include "simprr3.mm"
include "caovcl.mm"
include "eleq2.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "ralimdv.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "islly.mm"
include "sylanbrc.mm"

theorem txlly
  let cA: class A
  let cR: class R
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume txlly.1: |- ( ( j e. A /\ k e. A ) -> ( j tX k ) e. A )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint R j
  disjoint R k
  disjoint S k
  disjoint a b
  disjoint a j
  disjoint a k
  disjoint a r
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b j
  disjoint b k
  disjoint b r
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint j r
  disjoint j s
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k r
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R a
  disjoint R b
  disjoint R r
  disjoint R s
  disjoint R u
  disjoint R v
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S a
  disjoint S b
  disjoint S r
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint S z
  assert |- ( ( R e. Locally A /\ S e. Locally A ) -> ( R tX S ) e. Locally A )

  proof
    cR
    cA
    clly
    #
    wcel
    #
    cS
    @0
    wcel
    #
    wa
    #
    cR
    cS
    ctx
    co
    #
    ctop
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    wcel
    #
    @4
    @7
    crest
    co
    #
    cA
    wcel
    #
    wa
    #
    vz
    @4
    vx
    cv
    #
    cpw
    #
    cin
    #
    wrex
    #
    vy
    @12
    wral
    #
    vx
    @4
    wral
    @4
    @0
    wcel
    @1
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    @5
    @2
    cA
    cR
    llytop
    #
    cA
    cS
    llytop
    #
    cR
    cS
    txtop
    syl2an
    @3
    @16
    vx
    @4
    @3
    @12
    @4
    wcel
    @6
    vu
    cv
    #
    vv
    cv
    #
    cxp
    #
    wcel
    #
    @23
    @12
    wss
    #
    wa
    #
    vv
    cS
    wrex
    vu
    cR
    wrex
    #
    vy
    @12
    wral
    @16
    vu
    vv
    @12
    cR
    cS
    @0
    @0
    vy
    eltx
    @3
    @27
    @15
    vy
    @12
    @3
    @26
    @15
    vu
    vv
    cR
    cS
    @3
    @21
    cR
    wcel
    #
    @22
    cS
    wcel
    #
    wa
    #
    @26
    @15
    @3
    @30
    @26
    wa
    #
    wa
    #
    vr
    cv
    #
    @21
    wss
    #
    @6
    c1st
    cfv
    #
    @33
    wcel
    #
    cR
    @33
    crest
    co
    #
    cA
    wcel
    #
    w3a
    #
    vr
    cR
    wrex
    #
    vs
    cv
    #
    @22
    wss
    #
    @6
    c2nd
    cfv
    #
    @41
    wcel
    #
    cS
    @41
    crest
    co
    #
    cA
    wcel
    #
    w3a
    #
    vs
    cS
    wrex
    #
    @15
    @32
    @1
    @28
    @35
    @21
    wcel
    #
    @40
    @1
    @2
    @31
    simpll
    @3
    @28
    @29
    @26
    simprll
    @32
    @24
    @49
    @3
    @30
    @24
    @25
    simprrl
    #
    @6
    @21
    @22
    xp1st
    syl
    vr
    cA
    @35
    @21
    cR
    llyi
    syl3anc
    @32
    @2
    @29
    @43
    @22
    wcel
    #
    @48
    @1
    @2
    @31
    simplr
    @3
    @28
    @29
    @26
    simprlr
    @32
    @24
    @51
    @50
    @6
    @21
    @22
    xp2nd
    syl
    vs
    cA
    @43
    @22
    cS
    llyi
    syl3anc
    @40
    @48
    wa
    @39
    @47
    wa
    #
    vs
    cS
    wrex
    vr
    cR
    wrex
    @32
    @15
    @39
    @47
    vr
    vs
    cR
    cS
    reeanv
    @32
    @52
    @15
    vr
    vs
    cR
    cS
    @32
    @33
    cR
    wcel
    #
    @41
    cS
    wcel
    #
    wa
    #
    @52
    @15
    @32
    @55
    @52
    wa
    #
    wa
    #
    @33
    @41
    cxp
    #
    @14
    wcel
    @6
    @58
    wcel
    #
    @4
    @58
    crest
    co
    #
    cA
    wcel
    #
    @15
    @57
    @4
    @13
    @58
    @57
    @17
    @18
    @53
    @54
    @58
    @4
    wcel
    @1
    @17
    @2
    @31
    @56
    @19
    ad3antrrr
    #
    @2
    @18
    @1
    @31
    @56
    @20
    ad3antlr
    #
    @32
    @53
    @54
    @52
    simprll
    #
    @32
    @53
    @54
    @52
    simprlr
    #
    @33
    @41
    cR
    cS
    ctop
    ctop
    txopn
    syl22anc
    @57
    @58
    @12
    wss
    @58
    @13
    wcel
    @56
    @32
    @58
    @23
    @12
    @56
    @34
    @42
    @58
    @23
    wss
    @34
    @36
    @38
    @47
    @55
    simprl1
    @42
    @44
    @46
    @39
    @55
    simprr1
    @33
    @21
    @41
    @22
    xpss12
    syl2anc
    @3
    @30
    @24
    @25
    simprrr
    sylan9ssr
    @58
    @12
    vx
    vex
    elpw2
    sylibr
    elind
    @57
    @6
    @35
    @43
    cop
    #
    @58
    @32
    @6
    @66
    wceq
    #
    @56
    @32
    @24
    @67
    @50
    @6
    @21
    @22
    1st2nd2
    syl
    adantr
    @56
    @66
    @58
    wcel
    #
    @32
    @56
    @36
    @44
    @68
    @34
    @36
    @38
    @47
    @55
    simprl2
    @42
    @44
    @46
    @39
    @55
    simprr2
    @35
    @43
    @33
    @41
    opelxpi
    syl2anc
    adantl
    eqeltrd
    @57
    @60
    @37
    @45
    ctx
    co
    #
    cA
    @57
    @17
    @18
    @53
    @54
    @60
    @69
    wceq
    @62
    @63
    @64
    @65
    @33
    @41
    cR
    cS
    ctop
    ctop
    cR
    cS
    txrest
    syl22anc
    @56
    @69
    cA
    wcel
    #
    @32
    @56
    @38
    @46
    @70
    @34
    @36
    @38
    @47
    @55
    simprl3
    @42
    @44
    @46
    @39
    @55
    simprr3
    vj
    vk
    @37
    @45
    cA
    ctx
    txlly.1
    caovcl
    syl2anc
    adantl
    eqeltrd
    @11
    @59
    @61
    wa
    vz
    @58
    @14
    @7
    @58
    wceq
    #
    @8
    @59
    @10
    @61
    @7
    @58
    @6
    eleq2
    @71
    @9
    @60
    cA
    @7
    @58
    @4
    crest
    oveq2
    eleq1d
    anbi12d
    rspcev
    syl12anc
    expr
    rexlimdvva
    syl5bir
    mp2and
    expr
    rexlimdvva
    ralimdv
    sylbid
    ralrimiv
    vx
    vy
    vz
    cA
    @4
    islly
    sylanbrc
end
