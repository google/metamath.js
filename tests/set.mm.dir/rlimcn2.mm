include "co.mm"
include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "cv.mm"
include "cle.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "simprl.mm"
include "rlimi.mm"
include "simprr.mm"
include "reeanv.mm"
include "r19.26.mm"
include "cif.mm"
include "prth.mm"
include "wb.mm"
include "simplrl.mm"
include "simplrr.mm"
include "wss.mm"
include "cdm.mm"
include "eqid.mm"
include "dmmptd.mm"
include "rlimss.mm"
include "syl.mm"
include "eqsstr3d.mm"
include "ad2antrr.mm"
include "sselda.mm"
include "maxle.mm"
include "syl3anc.mm"
include "imbi1d.mm"
include "syl5ibr.mm"
include "ralimdva.mm"
include "ifcl.mm"
include "ancoms.mm"
include "ad2antlr.mm"
include "adantlr.mm"
include "jca.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "oveq1d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "sylan.mm"
include "imim2d.mm"
include "an32s.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "ex.mm"
include "com23.mm"
include "syld.mm"
include "syl5bir.mm"
include "rexlimdvva.mm"
include "mp2and.mm"
include "imp.mm"
include "syldan.mm"
include "cc.mm"
include "cxp.mm"
include "wf.mm"
include "fovrnd.mm"
include "rlim2.mm"
include "mpbird.mm"

theorem rlimcn2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume rlimcn2.1a: |- ( ( ph /\ z e. A ) -> B e. X )
  assume rlimcn2.1b: |- ( ( ph /\ z e. A ) -> C e. Y )
  assume rlimcn2.2a: |- ( ph -> R e. X )
  assume rlimcn2.2b: |- ( ph -> S e. Y )
  assume rlimcn2.3a: |- ( ph -> ( z e. A |-> B ) ~~>r R )
  assume rlimcn2.3b: |- ( ph -> ( z e. A |-> C ) ~~>r S )
  assume rlimcn2.4: |- ( ph -> F : ( X X. Y ) --> CC )
  assume rlimcn2.5: |- ( ( ph /\ x e. RR+ ) -> E. r e. RR+ E. s e. RR+ A. u e. X A. v e. Y ( ( ( abs ` ( u - R ) ) < r /\ ( abs ` ( v - S ) ) < s ) -> ( abs ` ( ( u F v ) - ( R F S ) ) ) < x ) )

  disjoint r s
  disjoint r x
  disjoint r z
  disjoint A r
  disjoint s x
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint r u
  disjoint r v
  disjoint F r
  disjoint s u
  disjoint s v
  disjoint F s
  disjoint u v
  disjoint u x
  disjoint u z
  disjoint F u
  disjoint v x
  disjoint v z
  disjoint F v
  disjoint F x
  disjoint F z
  disjoint R r
  disjoint R s
  disjoint R u
  disjoint R v
  disjoint R x
  disjoint R z
  disjoint B r
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B x
  disjoint ph r
  disjoint ph s
  disjoint ph x
  disjoint ph z
  disjoint S r
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S z
  disjoint C r
  disjoint C s
  disjoint C v
  disjoint C x
  disjoint X u
  disjoint X z
  disjoint Y u
  disjoint Y v
  disjoint Y z
  disjoint a b
  disjoint a c
  disjoint a r
  disjoint a s
  disjoint a x
  disjoint a z
  disjoint A a
  disjoint b c
  disjoint b r
  disjoint b s
  disjoint b x
  disjoint b z
  disjoint A b
  disjoint c r
  disjoint c s
  disjoint c x
  disjoint c z
  disjoint A c
  disjoint a u
  disjoint a v
  disjoint F a
  disjoint b u
  disjoint b v
  disjoint F b
  disjoint c u
  disjoint c v
  disjoint F c
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  assert |- ( ph -> ( z e. A |-> ( B F C ) ) ~~>r ( R F S ) )

  proof
    wph
    vz
    cA
    cB
    cC
    cF
    co
    #
    cmpt
    cR
    cS
    cF
    co
    #
    crli
    wbr
    vc
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    @0
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vc
    cr
    wrex
    #
    vx
    crp
    wral
    wph
    @11
    vx
    crp
    wph
    @7
    crp
    wcel
    vu
    cv
    #
    cR
    cmin
    co
    #
    cabs
    cfv
    #
    vr
    cv
    #
    clt
    wbr
    #
    vv
    cv
    #
    cS
    cmin
    co
    #
    cabs
    cfv
    #
    vs
    cv
    #
    clt
    wbr
    #
    wa
    #
    @12
    @17
    cF
    co
    #
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wi
    #
    vv
    cY
    wral
    vu
    cX
    wral
    #
    vs
    crp
    wrex
    vr
    crp
    wrex
    #
    @11
    rlimcn2.5
    wph
    @29
    @11
    wph
    @28
    @11
    vr
    vs
    crp
    crp
    wph
    @15
    crp
    wcel
    #
    @20
    crp
    wcel
    #
    wa
    #
    wa
    #
    va
    cv
    #
    @3
    cle
    wbr
    #
    cB
    cR
    cmin
    co
    #
    cabs
    cfv
    #
    @15
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    va
    cr
    wrex
    #
    vb
    cv
    #
    @3
    cle
    wbr
    #
    cC
    cS
    cmin
    co
    #
    cabs
    cfv
    #
    @20
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vb
    cr
    wrex
    #
    @28
    @11
    wi
    #
    @33
    va
    vz
    cA
    cB
    cR
    @15
    cX
    wph
    cB
    cX
    wcel
    #
    vz
    cA
    wral
    @32
    wph
    @51
    vz
    cA
    rlimcn2.1a
    ralrimiva
    adantr
    wph
    @30
    @31
    simprl
    wph
    vz
    cA
    cB
    cmpt
    #
    cR
    crli
    wbr
    #
    @32
    rlimcn2.3a
    adantr
    rlimi
    @33
    vb
    vz
    cA
    cC
    cS
    @20
    cY
    wph
    cC
    cY
    wcel
    #
    vz
    cA
    wral
    @32
    wph
    @54
    vz
    cA
    rlimcn2.1b
    ralrimiva
    adantr
    wph
    @30
    @31
    simprr
    wph
    vz
    cA
    cC
    cmpt
    cS
    crli
    wbr
    @32
    rlimcn2.3b
    adantr
    rlimi
    @41
    @49
    wa
    @40
    @48
    wa
    #
    vb
    cr
    wrex
    va
    cr
    wrex
    @33
    @50
    @40
    @48
    va
    vb
    cr
    cr
    reeanv
    @33
    @55
    @50
    va
    vb
    cr
    cr
    @55
    @39
    @47
    wa
    #
    vz
    cA
    wral
    #
    @33
    @34
    cr
    wcel
    #
    @42
    cr
    wcel
    #
    wa
    #
    wa
    #
    @50
    @39
    @47
    vz
    cA
    r19.26
    @61
    @57
    @34
    @42
    cle
    wbr
    #
    @42
    @34
    cif
    #
    @3
    cle
    wbr
    #
    @38
    @46
    wa
    #
    wi
    #
    vz
    cA
    wral
    #
    @50
    @61
    @56
    @66
    vz
    cA
    @56
    @66
    @61
    @3
    cA
    wcel
    #
    wa
    #
    @35
    @43
    wa
    #
    @65
    wi
    @35
    @38
    @43
    @46
    prth
    @69
    @64
    @70
    @65
    @69
    @58
    @59
    @3
    cr
    wcel
    @64
    @70
    wb
    @33
    @58
    @59
    @68
    simplrl
    @33
    @58
    @59
    @68
    simplrr
    @61
    cA
    cr
    @3
    wph
    cA
    cr
    wss
    @32
    @60
    wph
    cA
    @52
    cdm
    #
    cr
    wph
    vz
    @52
    cA
    cB
    cX
    @52
    eqid
    rlimcn2.1a
    dmmptd
    wph
    @53
    @71
    cr
    wss
    rlimcn2.3a
    cR
    @52
    rlimss
    syl
    eqsstr3d
    #
    ad2antrr
    sselda
    @34
    @42
    @3
    maxle
    syl3anc
    imbi1d
    syl5ibr
    ralimdva
    @61
    @28
    @67
    @11
    @61
    @28
    @67
    @11
    wi
    @61
    @28
    wa
    @63
    cr
    wcel
    #
    @67
    @64
    @8
    wi
    #
    vz
    cA
    wral
    #
    @11
    @60
    @73
    @33
    @28
    @59
    @58
    @73
    @62
    @42
    @34
    cr
    ifcl
    ancoms
    ad2antlr
    @33
    @28
    @67
    @75
    wi
    @60
    @33
    @28
    wa
    @66
    @74
    vz
    cA
    @33
    @68
    @28
    @66
    @74
    wi
    @33
    @68
    wa
    #
    @28
    wa
    @65
    @8
    @64
    @76
    @51
    @54
    wa
    @28
    @65
    @8
    wi
    #
    @76
    @51
    @54
    wph
    @68
    @51
    @32
    rlimcn2.1a
    adantlr
    wph
    @68
    @54
    @32
    rlimcn2.1b
    adantlr
    jca
    @27
    @77
    @38
    @21
    wa
    #
    cB
    @17
    cF
    co
    #
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wi
    vu
    vv
    cB
    cC
    cX
    cY
    @12
    cB
    wceq
    #
    @22
    @78
    @26
    @82
    @83
    @16
    @38
    @21
    @83
    @14
    @37
    @15
    clt
    @83
    @13
    @36
    cabs
    @12
    cB
    cR
    cmin
    oveq1
    fveq2d
    breq1d
    anbi1d
    @83
    @25
    @81
    @7
    clt
    @83
    @24
    @80
    cabs
    @83
    @23
    @79
    @1
    cmin
    @12
    cB
    @17
    cF
    oveq1
    oveq1d
    fveq2d
    breq1d
    imbi12d
    @17
    cC
    wceq
    #
    @78
    @65
    @82
    @8
    @84
    @21
    @46
    @38
    @84
    @19
    @45
    @20
    clt
    @84
    @18
    @44
    cabs
    @17
    cC
    cS
    cmin
    oveq1
    fveq2d
    breq1d
    anbi2d
    @84
    @81
    @6
    @7
    clt
    @84
    @80
    @5
    cabs
    @84
    @79
    @0
    @1
    cmin
    @17
    cC
    cB
    cF
    oveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspc2va
    sylan
    imim2d
    an32s
    ralimdva
    adantlr
    @10
    @75
    vc
    @63
    cr
    @2
    @63
    wceq
    #
    @9
    @74
    vz
    cA
    @85
    @4
    @64
    @8
    @2
    @63
    @3
    cle
    breq1
    imbi1d
    ralbidv
    rspcev
    syl6an
    ex
    com23
    syld
    syl5bir
    rexlimdvva
    syl5bir
    mp2and
    rexlimdvva
    imp
    syldan
    ralrimiva
    wph
    vx
    vc
    vz
    cA
    @0
    @1
    wph
    @0
    cc
    wcel
    vz
    cA
    wph
    @68
    wa
    cB
    cC
    cc
    cX
    cY
    cF
    wph
    cX
    cY
    cxp
    cc
    cF
    wf
    @68
    rlimcn2.4
    adantr
    rlimcn2.1a
    rlimcn2.1b
    fovrnd
    ralrimiva
    @72
    wph
    cR
    cS
    cc
    cX
    cY
    cF
    rlimcn2.4
    rlimcn2.2a
    rlimcn2.2b
    fovrnd
    rlim2
    mpbird
end
