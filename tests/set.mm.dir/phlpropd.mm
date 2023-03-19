include "clvec.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "csr.mm"
include "cbs.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "cmpt.mm"
include "crglmod.mm"
include "clmhm.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "cstv.mm"
include "wral.mm"
include "w3a.mm"
include "cphl.mm"
include "lvecpropd.mm"
include "eqtr3d.mm"
include "eleq1d.mm"
include "wa.mm"
include "oveqrspc2v.mm"
include "anass1rs.mm"
include "mpteq2dva.mm"
include "adantr.mm"
include "mpteq1d.mm"
include "3eqtr3d.mm"
include "rlmbas.mm"
include "eqtri.mm"
include "a1i.mm"
include "cvv.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "rlmsca.mm"
include "syl.mm"
include "cplusg.mm"
include "eqidd.mm"
include "cvsca.mm"
include "lmhmpropd.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "eleq12d.mm"
include "anabsan2.mm"
include "eqeq12d.mm"
include "grpidpropd.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "fveq12d.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "raleqdv.mm"
include "3bitr3d.mm"
include "3anbi123d.mm"
include "eqid.mm"
include "isphl.mm"
include "3bitr4g.mm"

theorem phlpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cP: class P
  let cF: class F
  let cK: class K
  let cL: class L
  let va: setvar a
  let vb: setvar b
  assume phlpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume phlpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume phlpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume phlpropd.4: |- ( ph -> F = ( Scalar ` K ) )
  assume phlpropd.5: |- ( ph -> F = ( Scalar ` L ) )
  assume phlpropd.6: |- P = ( Base ` F )
  assume phlpropd.7: |- ( ( ph /\ ( x e. P /\ y e. B ) ) -> ( x ( .s ` K ) y ) = ( x ( .s ` L ) y ) )
  assume phlpropd.8: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .i ` K ) y ) = ( x ( .i ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint ph y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint K a
  disjoint K b
  disjoint L a
  disjoint L b
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( K e. PreHil <-> L e. PreHil ) )

  proof
    wph
    cK
    clvec
    wcel
    #
    cK
    csca
    cfv
    #
    csr
    wcel
    #
    vb
    cK
    cbs
    cfv
    #
    vb
    cv
    #
    va
    cv
    #
    cK
    cip
    cfv
    #
    co
    #
    cmpt
    #
    cK
    @1
    crglmod
    cfv
    #
    clmhm
    co
    #
    wcel
    #
    @5
    @5
    @6
    co
    #
    @1
    c0g
    cfv
    #
    wceq
    #
    @5
    cK
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    @5
    @4
    @6
    co
    #
    @1
    cstv
    cfv
    #
    cfv
    #
    @7
    wceq
    #
    vb
    @3
    wral
    #
    w3a
    #
    va
    @3
    wral
    #
    w3a
    cL
    clvec
    wcel
    #
    cL
    csca
    cfv
    #
    csr
    wcel
    #
    vb
    cL
    cbs
    cfv
    #
    @4
    @5
    cL
    cip
    cfv
    #
    co
    #
    cmpt
    #
    cL
    @26
    crglmod
    cfv
    #
    clmhm
    co
    #
    wcel
    #
    @5
    @5
    @29
    co
    #
    @26
    c0g
    cfv
    #
    wceq
    #
    @5
    cL
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    @5
    @4
    @29
    co
    #
    @26
    cstv
    cfv
    #
    cfv
    #
    @30
    wceq
    #
    vb
    @28
    wral
    #
    w3a
    #
    va
    @28
    wral
    #
    w3a
    cK
    cphl
    wcel
    cL
    cphl
    wcel
    wph
    @0
    @25
    @2
    @27
    @24
    @47
    wph
    vx
    vy
    cB
    cP
    cF
    cK
    cL
    phlpropd.1
    phlpropd.2
    phlpropd.3
    phlpropd.4
    phlpropd.5
    phlpropd.6
    phlpropd.7
    lvecpropd
    wph
    @1
    @26
    csr
    wph
    cF
    @1
    @26
    phlpropd.4
    phlpropd.5
    eqtr3d
    #
    eleq1d
    wph
    @23
    va
    cB
    wral
    @46
    va
    cB
    wral
    @24
    @47
    wph
    @23
    @46
    va
    cB
    wph
    @5
    cB
    wcel
    #
    wa
    #
    @11
    @34
    @17
    @40
    @22
    @45
    @50
    @8
    @31
    @10
    @33
    @50
    vb
    cB
    @7
    cmpt
    vb
    cB
    @30
    cmpt
    @8
    @31
    @50
    vb
    cB
    @7
    @30
    wph
    @4
    cB
    wcel
    #
    @49
    @7
    @30
    wceq
    wph
    vx
    vy
    cB
    cB
    @6
    @29
    @4
    @5
    phlpropd.8
    oveqrspc2v
    anass1rs
    #
    mpteq2dva
    @50
    vb
    cB
    @3
    @7
    wph
    cB
    @3
    wceq
    @49
    phlpropd.1
    adantr
    #
    mpteq1d
    @50
    vb
    cB
    @28
    @30
    wph
    cB
    @28
    wceq
    @49
    phlpropd.2
    adantr
    #
    mpteq1d
    3eqtr3d
    wph
    @10
    @33
    wceq
    @49
    wph
    cK
    cF
    crglmod
    cfv
    #
    clmhm
    co
    cL
    @55
    clmhm
    co
    @10
    @33
    wph
    vx
    vy
    cB
    cP
    cP
    cP
    cF
    cF
    cK
    @55
    cL
    @55
    phlpropd.1
    cP
    @55
    cbs
    cfv
    #
    wceq
    wph
    cP
    cF
    cbs
    cfv
    @56
    phlpropd.6
    cF
    rlmbas
    eqtri
    a1i
    #
    phlpropd.2
    @57
    phlpropd.4
    wph
    cF
    cvv
    wcel
    cF
    @55
    csca
    cfv
    wceq
    wph
    cF
    @1
    cvv
    phlpropd.4
    cK
    csca
    fvex
    syl6eqel
    cF
    cvv
    rlmsca
    syl
    #
    phlpropd.5
    @58
    phlpropd.6
    phlpropd.6
    phlpropd.3
    wph
    vx
    cv
    #
    cP
    wcel
    vy
    cv
    #
    cP
    wcel
    wa
    wa
    #
    @59
    @60
    @55
    cplusg
    cfv
    co
    eqidd
    phlpropd.7
    @61
    @59
    @60
    @55
    cvsca
    cfv
    co
    eqidd
    lmhmpropd
    wph
    @55
    @9
    cK
    clmhm
    wph
    cF
    @1
    crglmod
    phlpropd.4
    fveq2d
    oveq2d
    wph
    @55
    @32
    cL
    clmhm
    wph
    cF
    @26
    crglmod
    phlpropd.5
    fveq2d
    oveq2d
    3eqtr3d
    adantr
    eleq12d
    @50
    @14
    @37
    @16
    @39
    @50
    @12
    @35
    @13
    @36
    wph
    @49
    @12
    @35
    wceq
    wph
    vx
    vy
    cB
    cB
    @6
    @29
    @5
    @5
    phlpropd.8
    oveqrspc2v
    anabsan2
    wph
    @13
    @36
    wceq
    @49
    wph
    @1
    @26
    c0g
    @48
    fveq2d
    adantr
    eqeq12d
    @50
    @15
    @38
    @5
    wph
    @15
    @38
    wceq
    @49
    wph
    vx
    vy
    cB
    cK
    cL
    phlpropd.1
    phlpropd.2
    phlpropd.3
    grpidpropd
    adantr
    eqeq2d
    imbi12d
    @50
    @21
    vb
    cB
    wral
    @44
    vb
    cB
    wral
    @22
    @45
    @50
    @21
    @44
    vb
    cB
    @50
    @51
    wa
    @20
    @43
    @7
    @30
    wph
    @49
    @51
    @20
    @43
    wceq
    wph
    @49
    @51
    wa
    #
    wa
    @18
    @41
    @19
    @42
    wph
    @19
    @42
    wceq
    @62
    wph
    @1
    @26
    cstv
    @48
    fveq2d
    adantr
    wph
    vx
    vy
    cB
    cB
    @6
    @29
    @5
    @4
    phlpropd.8
    oveqrspc2v
    fveq12d
    anassrs
    @52
    eqeq12d
    ralbidva
    @50
    @21
    vb
    cB
    @3
    @53
    raleqdv
    @50
    @44
    vb
    cB
    @28
    @54
    raleqdv
    3bitr3d
    3anbi123d
    ralbidva
    wph
    @23
    va
    cB
    @3
    phlpropd.1
    raleqdv
    wph
    @46
    va
    cB
    @28
    phlpropd.2
    raleqdv
    3bitr3d
    3anbi123d
    va
    vb
    @1
    @6
    @19
    @3
    cK
    @15
    @13
    @3
    eqid
    @1
    eqid
    @6
    eqid
    @15
    eqid
    @19
    eqid
    @13
    eqid
    isphl
    va
    vb
    @26
    @29
    @42
    @28
    cL
    @38
    @36
    @28
    eqid
    @26
    eqid
    @29
    eqid
    @38
    eqid
    @42
    eqid
    @36
    eqid
    isphl
    3bitr4g
end
