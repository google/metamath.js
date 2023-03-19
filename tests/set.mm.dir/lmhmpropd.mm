include "clmhm.mm"
include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cghm.mm"
include "csca.mm"
include "cfv.mm"
include "wceq.mm"
include "cvsca.mm"
include "cbs.mm"
include "wral.mm"
include "w3a.mm"
include "lmodpropd.mm"
include "anbi12d.mm"
include "oveqrspc2v.mm"
include "adantlr.mm"
include "fveq2d.mm"
include "simpll.mm"
include "simprl.mm"
include "simplrr.mm"
include "3eqtr4g.mm"
include "eleqtrrd.mm"
include "wf.mm"
include "simplrl.mm"
include "eqid.mm"
include "ghmf.mm"
include "syl.mm"
include "simprr.mm"
include "eleqtrd.mm"
include "ffvelrnd.mm"
include "syl12anc.mm"
include "eqeq12d.mm"
include "2ralbidva.mm"
include "pm5.32da.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "syl5eq.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "3anbi23d.mm"
include "ghmpropd.mm"
include "eleq2d.mm"
include "3anbi123d.mm"
include "3bitr3d.mm"
include "islmhm.mm"
include "eqrdv.mm"

theorem lmhmpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let vw: setvar w
  let vz: setvar z
  let vf: setvar f
  assume lmhmpropd.a: |- ( ph -> B = ( Base ` J ) )
  assume lmhmpropd.b: |- ( ph -> C = ( Base ` K ) )
  assume lmhmpropd.c: |- ( ph -> B = ( Base ` L ) )
  assume lmhmpropd.d: |- ( ph -> C = ( Base ` M ) )
  assume lmhmpropd.1: |- ( ph -> F = ( Scalar ` J ) )
  assume lmhmpropd.2: |- ( ph -> G = ( Scalar ` K ) )
  assume lmhmpropd.3: |- ( ph -> F = ( Scalar ` L ) )
  assume lmhmpropd.4: |- ( ph -> G = ( Scalar ` M ) )
  assume lmhmpropd.p: |- P = ( Base ` F )
  assume lmhmpropd.q: |- Q = ( Base ` G )
  assume lmhmpropd.e: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` J ) y ) = ( x ( +g ` L ) y ) )
  assume lmhmpropd.f: |- ( ( ph /\ ( x e. C /\ y e. C ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` M ) y ) )
  assume lmhmpropd.g: |- ( ( ph /\ ( x e. P /\ y e. B ) ) -> ( x ( .s ` J ) y ) = ( x ( .s ` L ) y ) )
  assume lmhmpropd.h: |- ( ( ph /\ ( x e. Q /\ y e. C ) ) -> ( x ( .s ` K ) y ) = ( x ( .s ` M ) y ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint M x
  disjoint M y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint ph y
  disjoint B x
  disjoint B y
  disjoint Q x
  disjoint Q y
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint G w
  disjoint G z
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint J f
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint x z
  disjoint y z
  disjoint J z
  disjoint K f
  disjoint K w
  disjoint K z
  disjoint L f
  disjoint L w
  disjoint L z
  disjoint M f
  disjoint M w
  disjoint M z
  disjoint P w
  disjoint P z
  disjoint f ph
  disjoint ph w
  disjoint ph z
  disjoint B w
  assert |- ( ph -> ( J LMHom K ) = ( L LMHom M ) )

  proof
    wph
    vf
    cJ
    cK
    clmhm
    co
    #
    cL
    cM
    clmhm
    co
    #
    wph
    cJ
    clmod
    wcel
    #
    cK
    clmod
    wcel
    #
    wa
    #
    vf
    cv
    #
    cJ
    cK
    cghm
    co
    #
    wcel
    #
    cK
    csca
    cfv
    #
    cJ
    csca
    cfv
    #
    wceq
    #
    vz
    cv
    #
    vw
    cv
    #
    cJ
    cvsca
    cfv
    #
    co
    #
    @5
    cfv
    #
    @11
    @12
    @5
    cfv
    #
    cK
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vw
    cJ
    cbs
    cfv
    #
    wral
    #
    vz
    @9
    cbs
    cfv
    #
    wral
    #
    w3a
    #
    wa
    cL
    clmod
    wcel
    #
    cM
    clmod
    wcel
    #
    wa
    #
    @5
    cL
    cM
    cghm
    co
    #
    wcel
    #
    cM
    csca
    cfv
    #
    cL
    csca
    cfv
    #
    wceq
    #
    @11
    @12
    cL
    cvsca
    cfv
    #
    co
    #
    @5
    cfv
    #
    @11
    @16
    cM
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vw
    cL
    cbs
    cfv
    #
    wral
    #
    vz
    @31
    cbs
    cfv
    #
    wral
    #
    w3a
    #
    wa
    @5
    @0
    wcel
    @5
    @1
    wcel
    wph
    @4
    @27
    @24
    @43
    wph
    @2
    @25
    @3
    @26
    wph
    vx
    vy
    cB
    cP
    cF
    cJ
    cL
    lmhmpropd.a
    lmhmpropd.c
    lmhmpropd.e
    lmhmpropd.1
    lmhmpropd.3
    lmhmpropd.p
    lmhmpropd.g
    lmodpropd
    wph
    vx
    vy
    cC
    cQ
    cG
    cK
    cM
    lmhmpropd.b
    lmhmpropd.d
    lmhmpropd.f
    lmhmpropd.2
    lmhmpropd.4
    lmhmpropd.q
    lmhmpropd.h
    lmodpropd
    anbi12d
    wph
    @7
    cG
    cF
    wceq
    #
    @19
    vw
    cB
    wral
    #
    vz
    cP
    wral
    #
    w3a
    #
    @7
    @44
    @38
    vw
    cB
    wral
    #
    vz
    cP
    wral
    #
    w3a
    #
    @24
    @43
    wph
    @7
    @44
    wa
    #
    @46
    wa
    @51
    @49
    wa
    @47
    @50
    wph
    @51
    @46
    @49
    wph
    @51
    wa
    #
    @19
    @38
    vz
    vw
    cP
    cB
    @52
    @11
    cP
    wcel
    #
    @12
    cB
    wcel
    #
    wa
    #
    wa
    #
    @15
    @35
    @18
    @37
    @56
    @14
    @34
    @5
    wph
    @55
    @14
    @34
    wceq
    @51
    wph
    vx
    vy
    cP
    cB
    @13
    @33
    @11
    @12
    lmhmpropd.g
    oveqrspc2v
    adantlr
    fveq2d
    @56
    wph
    @11
    cQ
    wcel
    @16
    cC
    wcel
    @18
    @37
    wceq
    wph
    @51
    @55
    simpll
    #
    @56
    @11
    cP
    cQ
    @52
    @53
    @54
    simprl
    @56
    cG
    cbs
    cfv
    cF
    cbs
    cfv
    #
    cQ
    cP
    @56
    cG
    cF
    cbs
    wph
    @7
    @44
    @55
    simplrr
    fveq2d
    lmhmpropd.q
    lmhmpropd.p
    3eqtr4g
    eleqtrrd
    @56
    @16
    cK
    cbs
    cfv
    #
    cC
    @56
    @20
    @59
    @12
    @5
    @56
    @7
    @20
    @59
    @5
    wf
    wph
    @7
    @44
    @55
    simplrl
    cJ
    cK
    @5
    @20
    @59
    @20
    eqid
    #
    @59
    eqid
    ghmf
    syl
    @56
    @12
    cB
    @20
    @52
    @53
    @54
    simprr
    @56
    wph
    cB
    @20
    wceq
    @57
    lmhmpropd.a
    syl
    eleqtrd
    ffvelrnd
    @56
    wph
    cC
    @59
    wceq
    @57
    lmhmpropd.b
    syl
    eleqtrrd
    wph
    vx
    vy
    cQ
    cC
    @17
    @36
    @11
    @16
    lmhmpropd.h
    oveqrspc2v
    syl12anc
    eqeq12d
    2ralbidva
    pm5.32da
    @7
    @44
    @46
    df-3an
    @7
    @44
    @49
    df-3an
    3bitr4g
    wph
    @44
    @10
    @46
    @23
    @7
    wph
    cG
    @8
    cF
    @9
    lmhmpropd.2
    lmhmpropd.1
    eqeq12d
    wph
    @45
    @21
    vz
    cP
    @22
    wph
    cP
    @58
    @22
    lmhmpropd.p
    wph
    cF
    @9
    cbs
    lmhmpropd.1
    fveq2d
    syl5eq
    wph
    @19
    vw
    cB
    @20
    lmhmpropd.a
    raleqdv
    raleqbidv
    3anbi23d
    wph
    @7
    @29
    @44
    @32
    @49
    @42
    wph
    @6
    @28
    @5
    wph
    vx
    vy
    cB
    cC
    cJ
    cK
    cL
    cM
    lmhmpropd.a
    lmhmpropd.b
    lmhmpropd.c
    lmhmpropd.d
    lmhmpropd.e
    lmhmpropd.f
    ghmpropd
    eleq2d
    wph
    cG
    @30
    cF
    @31
    lmhmpropd.4
    lmhmpropd.3
    eqeq12d
    wph
    @48
    @40
    vz
    cP
    @41
    wph
    cP
    @58
    @41
    lmhmpropd.p
    wph
    cF
    @31
    cbs
    lmhmpropd.3
    fveq2d
    syl5eq
    wph
    @38
    vw
    cB
    @39
    lmhmpropd.c
    raleqdv
    raleqbidv
    3anbi123d
    3bitr3d
    anbi12d
    vz
    vw
    @22
    cJ
    cK
    @13
    @17
    @20
    @5
    @9
    @8
    @9
    eqid
    @8
    eqid
    @22
    eqid
    @60
    @13
    eqid
    @17
    eqid
    islmhm
    vz
    vw
    @41
    cL
    cM
    @33
    @36
    @39
    @5
    @31
    @30
    @31
    eqid
    @30
    eqid
    @41
    eqid
    @39
    eqid
    @33
    eqid
    @36
    eqid
    islmhm
    3bitr4g
    eqrdv
end
