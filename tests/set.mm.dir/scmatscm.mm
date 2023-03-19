include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "cur.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "eqid.mm"
include "scmatscmid.mm"
include "3expa.mm"
include "oveq1.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csb.mm"
include "simpr.mm"
include "ad4antr.mm"
include "simpl.mm"
include "adantr.mm"
include "matring.mm"
include "ringidcl.mm"
include "syl.mm"
include "anim1i.mm"
include "ancomd.mm"
include "matvscl.mm"
include "syl2anc.mm"
include "matmulcell.mm"
include "syl3anc.mm"
include "weq.mm"
include "c0g.mm"
include "cif.mm"
include "cvv.mm"
include "w3a.mm"
include "cmpt2.mm"
include "df-3an.mm"
include "sylibr.mm"
include "ad3antrrr.mm"
include "matsc.mm"
include "eqeq12.mm"
include "ifbid.mm"
include "adantl.mm"
include "vex.mm"
include "fvex.mm"
include "ifex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "ovif.mm"
include "simp-6r.mm"
include "simplrr.mm"
include "ad2antrr.mm"
include "matecld.mm"
include "ringlz.mm"
include "ifeq2d.mm"
include "syl5eq.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "wb.mm"
include "equcom.mm"
include "ifbi.mm"
include "ax-mp.mm"
include "mpteq2i.mm"
include "cbs.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "ringcl.mm"
include "ralrimiva.mm"
include "gsummpt1n0.mm"
include "3eqtrd.mm"
include "csbov2g.mm"
include "csbov1g.mm"
include "csbvarg.mm"
include "eqtrd.mm"
include "matvscacell.mm"
include "eqtr4d.mm"
include "ralrimivva.mm"
include "eqmat.mm"
include "mpbird.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "ralrimdva.mm"
include "reximdva.mm"
include "mpd.mm"

theorem scmatscm
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let c.xp: class .X.
  let vm: setvar m
  let c.as: class .*
  let cK: class K
  let cN: class N
  let vc: setvar c
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume scmatscm.k: |- K = ( Base ` R )
  assume scmatscm.a: |- A = ( N Mat R )
  assume scmatscm.b: |- B = ( Base ` A )
  assume scmatscm.t: |- .* = ( .s ` A )
  assume scmatscm.m: |- .X. = ( .r ` A )
  assume scmatscm.c: |- S = ( N ScMat R )

  disjoint A m
  disjoint C c
  disjoint C m
  disjoint K c
  disjoint K m
  disjoint N c
  disjoint N m
  disjoint c m
  disjoint R c
  disjoint R m
  disjoint S c
  disjoint S m
  disjoint .* m
  disjoint A i
  disjoint A j
  disjoint A k
  disjoint A x
  disjoint A y
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j m
  disjoint j x
  disjoint j y
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint x y
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint c k
  disjoint c x
  disjoint c y
  disjoint C i
  disjoint C j
  disjoint K k
  disjoint K x
  disjoint K y
  disjoint K i
  disjoint K j
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint N i
  disjoint N j
  disjoint c i
  disjoint c j
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint R i
  disjoint R j
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint S i
  disjoint S j
  disjoint .* i
  disjoint .* j
  disjoint .* k
  disjoint .* x
  disjoint .* y
  disjoint .X. i
  disjoint .X. j
  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ C e. S ) -> E. c e. K A. m e. B ( C .X. m ) = ( c .* m ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cC
    cS
    wcel
    #
    wa
    #
    cC
    vc
    cv
    #
    cA
    cur
    cfv
    #
    c.as
    co
    #
    wceq
    #
    vc
    cK
    wrex
    #
    cC
    vm
    cv
    #
    c.xp
    co
    #
    @5
    @10
    c.as
    co
    #
    wceq
    #
    vm
    cB
    wral
    #
    vc
    cK
    wrex
    @0
    @1
    @3
    @9
    cA
    cB
    cR
    cS
    c.as
    @6
    cK
    cC
    cN
    crg
    vc
    scmatscm.k
    scmatscm.a
    scmatscm.b
    @6
    eqid
    #
    scmatscm.t
    scmatscm.c
    scmatscmid
    3expa
    @4
    @8
    @14
    vc
    cK
    @4
    @5
    cK
    wcel
    #
    wa
    #
    @8
    @13
    vm
    cB
    @17
    @10
    cB
    wcel
    #
    wa
    #
    @8
    @13
    @8
    @19
    @11
    @7
    @10
    c.xp
    co
    #
    @12
    cC
    @7
    @10
    c.xp
    oveq1
    @19
    @20
    @12
    wceq
    #
    vi
    cv
    #
    vj
    cv
    #
    @20
    co
    #
    @22
    @23
    @12
    co
    #
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @19
    @26
    vi
    vj
    cN
    cN
    @19
    @22
    cN
    wcel
    #
    @23
    cN
    wcel
    #
    wa
    #
    wa
    #
    @24
    @5
    @22
    @23
    @10
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @25
    @31
    @24
    cR
    vk
    cN
    @22
    vk
    cv
    #
    @7
    co
    #
    @35
    @23
    @10
    co
    #
    @33
    co
    #
    cmpt
    #
    cgsu
    co
    #
    vk
    @22
    @5
    @37
    @33
    co
    #
    csb
    #
    @34
    @31
    @1
    @7
    cB
    wcel
    #
    @18
    wa
    #
    @30
    @24
    @40
    wceq
    @2
    @1
    @3
    @16
    @18
    @30
    @0
    @1
    simpr
    ad4antr
    #
    @19
    @44
    @30
    @17
    @43
    @18
    @17
    @2
    @16
    @6
    cB
    wcel
    #
    wa
    @43
    @4
    @2
    @16
    @2
    @3
    simpl
    #
    adantr
    @17
    @46
    @16
    @4
    @46
    @16
    @2
    @46
    @3
    @2
    cA
    crg
    wcel
    #
    @46
    cA
    cR
    cN
    scmatscm.a
    matring
    #
    cB
    cA
    @6
    scmatscm.b
    @15
    ringidcl
    syl
    adantr
    anim1i
    ancomd
    cA
    cB
    @5
    cR
    c.as
    cK
    cN
    @6
    scmatscm.k
    scmatscm.a
    scmatscm.b
    scmatscm.t
    matvscl
    syl2anc
    #
    anim1i
    adantr
    @19
    @30
    simpr
    #
    cA
    cB
    cR
    @33
    c.xp
    vk
    @22
    @23
    cN
    @7
    @10
    scmatscm.a
    scmatscm.b
    @33
    eqid
    #
    scmatscm.m
    matmulcell
    syl3anc
    @31
    @40
    cR
    vk
    cN
    vi
    vk
    weq
    #
    @5
    cR
    c0g
    cfv
    #
    cif
    #
    @37
    @33
    co
    #
    cmpt
    #
    cgsu
    co
    cR
    vk
    cN
    @53
    @41
    @54
    cif
    #
    cmpt
    #
    cgsu
    co
    @42
    @31
    @39
    @57
    cR
    cgsu
    @31
    vk
    cN
    @38
    @56
    @31
    @35
    cN
    wcel
    #
    wa
    #
    @36
    @55
    @37
    @33
    @61
    vx
    vy
    @22
    @35
    cN
    cN
    vx
    vy
    weq
    #
    @5
    @54
    cif
    #
    @55
    @7
    cvv
    @61
    @0
    @1
    @16
    w3a
    #
    @7
    vx
    vy
    cN
    cN
    @63
    cmpt2
    wceq
    @17
    @64
    @18
    @30
    @60
    @17
    @2
    @16
    wa
    @64
    @4
    @2
    @16
    @47
    anim1i
    @0
    @1
    @16
    df-3an
    sylibr
    ad3antrrr
    cA
    cR
    c.as
    vx
    vy
    cK
    @5
    cN
    @54
    scmatscm.a
    scmatscm.k
    scmatscm.t
    @54
    eqid
    #
    matsc
    syl
    vx
    vi
    weq
    vy
    vk
    weq
    wa
    #
    @63
    @55
    wceq
    @61
    @66
    @62
    @53
    @5
    @54
    vx
    cv
    @22
    vy
    cv
    @35
    eqeq12
    ifbid
    adantl
    @31
    @28
    @60
    @30
    @28
    @19
    @28
    @29
    simpl
    adantl
    #
    adantr
    @31
    @60
    simpr
    #
    @55
    cvv
    wcel
    @61
    @53
    @5
    @54
    vc
    vex
    cR
    c0g
    fvex
    ifex
    a1i
    ovmpt2d
    oveq1d
    mpteq2dva
    oveq2d
    @31
    @57
    @59
    cR
    cgsu
    @31
    vk
    cN
    @56
    @58
    @61
    @56
    @53
    @41
    @54
    @37
    @33
    co
    #
    cif
    @58
    @53
    @5
    @54
    @37
    @33
    ovif
    @61
    @53
    @69
    @54
    @41
    @61
    @1
    @37
    cK
    wcel
    @69
    @54
    wceq
    @0
    @1
    @3
    @16
    @18
    @30
    @60
    simp-6r
    #
    @61
    cA
    cB
    cR
    @35
    @23
    cK
    @10
    cN
    scmatscm.a
    scmatscm.k
    scmatscm.b
    @68
    @19
    @28
    @29
    @60
    simplrr
    #
    @19
    @18
    @30
    @60
    @17
    @18
    simpr
    #
    ad2antrr
    #
    matecld
    cK
    cR
    @33
    @37
    @54
    scmatscm.k
    @52
    @65
    ringlz
    syl2anc
    ifeq2d
    syl5eq
    mpteq2dva
    oveq2d
    @31
    @41
    vk
    @59
    cR
    cN
    cfn
    @22
    @54
    @65
    @2
    cR
    cmnd
    wcel
    #
    @3
    @16
    @18
    @30
    @1
    @74
    @0
    cR
    ringmnd
    adantl
    ad4antr
    @2
    @0
    @3
    @16
    @18
    @30
    @0
    @1
    simpl
    ad4antr
    @67
    vk
    cN
    @58
    vk
    vi
    weq
    #
    @41
    @54
    cif
    #
    @53
    @75
    wb
    @58
    @76
    wceq
    vi
    vk
    equcom
    @53
    @75
    @41
    @54
    ifbi
    ax-mp
    mpteq2i
    @31
    @41
    cR
    cbs
    cfv
    #
    wcel
    #
    vk
    cN
    @61
    @1
    @5
    @77
    wcel
    #
    @37
    @77
    wcel
    @78
    @70
    @17
    @79
    @18
    @30
    @60
    @16
    @79
    @4
    @16
    @79
    cK
    @77
    @5
    scmatscm.k
    eleq2i
    biimpi
    adantl
    ad3antrrr
    @61
    cA
    cB
    cR
    @35
    @23
    @77
    @10
    cN
    scmatscm.a
    @77
    eqid
    #
    scmatscm.b
    @68
    @71
    @73
    matecld
    @77
    cR
    @33
    @5
    @37
    @80
    @52
    ringcl
    syl3anc
    ralrimiva
    gsummpt1n0
    3eqtrd
    @30
    @42
    @34
    wceq
    #
    @19
    @28
    @81
    @29
    @28
    @42
    @5
    vk
    @22
    @37
    csb
    #
    @33
    co
    @34
    vk
    @22
    @5
    @37
    @33
    cN
    csbov2g
    @28
    @82
    @32
    @5
    @33
    @28
    @82
    vk
    @22
    @35
    csb
    #
    @23
    @10
    co
    @32
    vk
    @22
    @35
    @23
    @10
    cN
    csbov1g
    @28
    @83
    @22
    @23
    @10
    vk
    @22
    cN
    csbvarg
    oveq1d
    eqtrd
    oveq2d
    eqtrd
    adantr
    adantl
    3eqtrd
    @31
    @1
    @16
    @18
    wa
    #
    @30
    @25
    @34
    wceq
    @45
    @19
    @84
    @30
    @17
    @16
    @18
    @4
    @16
    simpr
    anim1i
    #
    adantr
    @51
    cA
    cB
    cR
    c.as
    @33
    @22
    @23
    cK
    cN
    @5
    @10
    scmatscm.a
    scmatscm.b
    scmatscm.k
    scmatscm.t
    @52
    matvscacell
    syl3anc
    eqtr4d
    ralrimivva
    @19
    @20
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @21
    @27
    wb
    @19
    @48
    @43
    @18
    @86
    @2
    @48
    @3
    @16
    @18
    @49
    ad3antrrr
    @17
    @43
    @18
    @50
    adantr
    @72
    cB
    cA
    c.xp
    @7
    @10
    scmatscm.b
    scmatscm.m
    ringcl
    syl3anc
    @19
    @2
    @84
    @87
    @4
    @2
    @16
    @18
    @47
    ad2antrr
    @85
    cA
    cB
    @5
    cR
    c.as
    cK
    cN
    @10
    scmatscm.k
    scmatscm.a
    scmatscm.b
    scmatscm.t
    matvscl
    syl2anc
    cA
    cB
    cR
    vi
    vj
    cN
    @20
    @12
    scmatscm.a
    scmatscm.b
    eqmat
    syl2anc
    mpbird
    sylan9eqr
    ex
    ralrimdva
    reximdva
    mpd
end
