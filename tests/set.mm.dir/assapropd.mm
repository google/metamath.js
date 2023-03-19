include "clmod.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "casa.mm"
include "wi.mm"
include "assalmod.mm"
include "assaring.mm"
include "jca.mm"
include "a1i.mm"
include "lmodpropd.mm"
include "syl5ibr.mm"
include "ringpropd.mm"
include "jcad.mm"
include "wb.mm"
include "csca.mm"
include "cfv.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cmulr.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "eqtr3d.mm"
include "eleq1d.mm"
include "3anbi123d.mm"
include "adantr.mm"
include "simpll.mm"
include "simplrl.mm"
include "simprl.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "syl.mm"
include "eleqtrd.mm"
include "simprrl.mm"
include "eqid.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "simprrr.mm"
include "oveqrspc2v.mm"
include "syl12anc.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "simplrr.mm"
include "ringcl.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "anassrs.mm"
include "2ralbidva.mm"
include "ralbidva.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "3bitr3d.mm"
include "isassa.mm"
include "3bitr4g.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem assapropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cP: class P
  let cF: class F
  let cK: class K
  let cL: class L
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  assume assapropd.1: |- ( ph -> B = ( Base ` K ) )
  assume assapropd.2: |- ( ph -> B = ( Base ` L ) )
  assume assapropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume assapropd.4: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` L ) y ) )
  assume assapropd.5: |- ( ph -> F = ( Scalar ` K ) )
  assume assapropd.6: |- ( ph -> F = ( Scalar ` L ) )
  assume assapropd.7: |- P = ( Base ` F )
  assume assapropd.8: |- ( ( ph /\ ( x e. P /\ y e. B ) ) -> ( x ( .s ` K ) y ) = ( x ( .s ` L ) y ) )

  disjoint x y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint ph y
  disjoint B x
  disjoint B y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint K r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint K w
  disjoint x z
  disjoint y z
  disjoint K z
  disjoint L r
  disjoint L w
  disjoint L z
  disjoint P r
  disjoint P w
  disjoint P z
  disjoint ph r
  disjoint ph w
  disjoint ph z
  disjoint B w
  disjoint B z
  assert |- ( ph -> ( K e. AssAlg <-> L e. AssAlg ) )

  proof
    wph
    cK
    clmod
    wcel
    #
    cK
    crg
    wcel
    #
    wa
    #
    cK
    casa
    wcel
    #
    cL
    casa
    wcel
    #
    @3
    @2
    wi
    wph
    @3
    @0
    @1
    cK
    assalmod
    cK
    assaring
    jca
    a1i
    wph
    @4
    @0
    @1
    @4
    @0
    wph
    cL
    clmod
    wcel
    #
    cL
    assalmod
    wph
    vx
    vy
    cB
    cP
    cF
    cK
    cL
    assapropd.1
    assapropd.2
    assapropd.3
    assapropd.5
    assapropd.6
    assapropd.7
    assapropd.8
    lmodpropd
    #
    syl5ibr
    @4
    @1
    wph
    cL
    crg
    wcel
    #
    cL
    assaring
    wph
    vx
    vy
    cB
    cK
    cL
    assapropd.1
    assapropd.2
    assapropd.3
    assapropd.4
    ringpropd
    #
    syl5ibr
    jcad
    wph
    @2
    @3
    @4
    wb
    wph
    @2
    wa
    #
    @0
    @1
    cK
    csca
    cfv
    #
    ccrg
    wcel
    #
    w3a
    #
    vr
    cv
    #
    vz
    cv
    #
    cK
    cvsca
    cfv
    #
    co
    #
    vw
    cv
    #
    cK
    cmulr
    cfv
    #
    co
    #
    @13
    @14
    @17
    @18
    co
    #
    @15
    co
    #
    wceq
    #
    @14
    @13
    @17
    @15
    co
    #
    @18
    co
    #
    @21
    wceq
    #
    wa
    #
    vw
    cK
    cbs
    cfv
    #
    wral
    #
    vz
    @27
    wral
    #
    vr
    @10
    cbs
    cfv
    #
    wral
    #
    wa
    @5
    @7
    cL
    csca
    cfv
    #
    ccrg
    wcel
    #
    w3a
    #
    @13
    @14
    cL
    cvsca
    cfv
    #
    co
    #
    @17
    cL
    cmulr
    cfv
    #
    co
    #
    @13
    @14
    @17
    @37
    co
    #
    @35
    co
    #
    wceq
    #
    @14
    @13
    @17
    @35
    co
    #
    @37
    co
    #
    @40
    wceq
    #
    wa
    #
    vw
    cL
    cbs
    cfv
    #
    wral
    #
    vz
    @46
    wral
    #
    vr
    @32
    cbs
    cfv
    #
    wral
    #
    wa
    @3
    @4
    @9
    @12
    @34
    @31
    @50
    wph
    @12
    @34
    wb
    @2
    wph
    @0
    @5
    @1
    @7
    @11
    @33
    @6
    @8
    wph
    @10
    @32
    ccrg
    wph
    cF
    @10
    @32
    assapropd.5
    assapropd.6
    eqtr3d
    eleq1d
    3anbi123d
    adantr
    @9
    @26
    vw
    cB
    wral
    #
    vz
    cB
    wral
    #
    vr
    cP
    wral
    @45
    vw
    cB
    wral
    #
    vz
    cB
    wral
    #
    vr
    cP
    wral
    @31
    @50
    @9
    @52
    @54
    vr
    cP
    @9
    @13
    cP
    wcel
    #
    wa
    @26
    @45
    vz
    vw
    cB
    cB
    @9
    @55
    @14
    cB
    wcel
    #
    @17
    cB
    wcel
    #
    wa
    #
    @26
    @45
    wb
    @9
    @55
    @58
    wa
    #
    wa
    #
    @22
    @41
    @25
    @44
    @60
    @19
    @38
    @21
    @40
    @60
    @19
    @16
    @17
    @37
    co
    #
    @38
    @60
    wph
    @16
    cB
    wcel
    @57
    @19
    @61
    wceq
    wph
    @2
    @59
    simpll
    #
    @60
    @16
    @27
    cB
    @60
    @0
    @13
    @30
    wcel
    #
    @14
    @27
    wcel
    #
    @16
    @27
    wcel
    wph
    @0
    @1
    @59
    simplrl
    #
    @60
    @13
    cP
    @30
    @9
    @55
    @58
    simprl
    #
    @60
    wph
    cP
    @30
    wceq
    #
    @62
    wph
    cP
    cF
    cbs
    cfv
    #
    @30
    assapropd.7
    wph
    cF
    @10
    cbs
    assapropd.5
    fveq2d
    syl5eq
    #
    syl
    eleqtrd
    #
    @60
    @14
    cB
    @27
    @9
    @55
    @56
    @57
    simprrl
    #
    @60
    wph
    cB
    @27
    wceq
    #
    @62
    assapropd.1
    syl
    #
    eleqtrd
    #
    @13
    @15
    @10
    @30
    @27
    cK
    @14
    @27
    eqid
    #
    @10
    eqid
    #
    @15
    eqid
    #
    @30
    eqid
    #
    lmodvscl
    syl3anc
    @73
    eleqtrrd
    @9
    @55
    @56
    @57
    simprrr
    #
    wph
    vx
    vy
    cB
    cB
    @18
    @37
    @16
    @17
    assapropd.4
    oveqrspc2v
    syl12anc
    @60
    @16
    @36
    @17
    @37
    @60
    wph
    @55
    @56
    @16
    @36
    wceq
    @62
    @66
    @71
    wph
    vx
    vy
    cP
    cB
    @15
    @35
    @13
    @14
    assapropd.8
    oveqrspc2v
    syl12anc
    oveq1d
    eqtrd
    @60
    @21
    @13
    @20
    @35
    co
    #
    @40
    @60
    wph
    @55
    @20
    cB
    wcel
    @21
    @80
    wceq
    @62
    @66
    @60
    @20
    @27
    cB
    @60
    @1
    @64
    @17
    @27
    wcel
    #
    @20
    @27
    wcel
    wph
    @0
    @1
    @59
    simplrr
    @74
    @60
    @17
    cB
    @27
    @79
    @73
    eleqtrd
    #
    @27
    cK
    @18
    @14
    @17
    @75
    @18
    eqid
    #
    ringcl
    syl3anc
    @73
    eleqtrrd
    wph
    vx
    vy
    cP
    cB
    @15
    @35
    @13
    @20
    assapropd.8
    oveqrspc2v
    syl12anc
    @60
    @20
    @39
    @13
    @35
    @60
    wph
    @56
    @57
    @20
    @39
    wceq
    @62
    @71
    @79
    wph
    vx
    vy
    cB
    cB
    @18
    @37
    @14
    @17
    assapropd.4
    oveqrspc2v
    syl12anc
    oveq2d
    eqtrd
    #
    eqeq12d
    @60
    @24
    @43
    @21
    @40
    @60
    @24
    @14
    @23
    @37
    co
    #
    @43
    @60
    wph
    @56
    @23
    cB
    wcel
    @24
    @85
    wceq
    @62
    @71
    @60
    @23
    @27
    cB
    @60
    @0
    @63
    @81
    @23
    @27
    wcel
    @65
    @70
    @82
    @13
    @15
    @10
    @30
    @27
    cK
    @17
    @75
    @76
    @77
    @78
    lmodvscl
    syl3anc
    @73
    eleqtrrd
    wph
    vx
    vy
    cB
    cB
    @18
    @37
    @14
    @23
    assapropd.4
    oveqrspc2v
    syl12anc
    @60
    @23
    @42
    @14
    @37
    @60
    wph
    @55
    @57
    @23
    @42
    wceq
    @62
    @66
    @79
    wph
    vx
    vy
    cP
    cB
    @15
    @35
    @13
    @17
    assapropd.8
    oveqrspc2v
    syl12anc
    oveq2d
    eqtrd
    @84
    eqeq12d
    anbi12d
    anassrs
    2ralbidva
    ralbidva
    @9
    @52
    @29
    vr
    cP
    @30
    wph
    @67
    @2
    @69
    adantr
    @9
    @51
    @28
    vz
    cB
    @27
    wph
    @72
    @2
    assapropd.1
    adantr
    #
    @9
    @26
    vw
    cB
    @27
    @86
    raleqdv
    raleqbidv
    raleqbidv
    @9
    @54
    @48
    vr
    cP
    @49
    wph
    cP
    @49
    wceq
    @2
    wph
    cP
    @68
    @49
    assapropd.7
    wph
    cF
    @32
    cbs
    assapropd.6
    fveq2d
    syl5eq
    adantr
    @9
    @53
    @47
    vz
    cB
    @46
    wph
    cB
    @46
    wceq
    @2
    assapropd.2
    adantr
    #
    @9
    @45
    vw
    cB
    @46
    @87
    raleqdv
    raleqbidv
    raleqbidv
    3bitr3d
    anbi12d
    vz
    vw
    @30
    @15
    @18
    @10
    @27
    cK
    vr
    @75
    @76
    @78
    @77
    @83
    isassa
    vz
    vw
    @49
    @35
    @37
    @32
    @46
    cL
    vr
    @46
    eqid
    @32
    eqid
    @49
    eqid
    @35
    eqid
    @37
    eqid
    isassa
    3bitr4g
    ex
    pm5.21ndd
end
