include "clbs.mm"
include "cfv.mm"
include "cv.mm"
include "cbs.mm"
include "wss.mm"
include "clspn.mm"
include "wceq.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "c0g.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "simplll.mm"
include "eldifi.mm"
include "adantl.mm"
include "simpr.mm"
include "sselda.mm"
include "adantr.mm"
include "oveqrspc2v.mm"
include "syl12anc.mm"
include "csca.mm"
include "fveq2i.mm"
include "syl6eq.mm"
include "lsppropd.mm"
include "syl.mm"
include "fveq1d.mm"
include "eleq12d.mm"
include "notbid.mm"
include "ralbidva.mm"
include "ad2antrr.mm"
include "difeq1d.mm"
include "raleqdv.mm"
include "grpidpropd.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "3bitr3d.mm"
include "anbi2d.mm"
include "pm5.32da.mm"
include "sseq2d.mm"
include "anbi1d.mm"
include "eqtr3d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "3anass.mm"
include "3bitr4g.mm"
include "cvv.mm"
include "wb.mm"
include "eqid.mm"
include "islbs.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem lbspropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cW: class W
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  assume lbspropd.b1: |- ( ph -> B = ( Base ` K ) )
  assume lbspropd.b2: |- ( ph -> B = ( Base ` L ) )
  assume lbspropd.w: |- ( ph -> B C_ W )
  assume lbspropd.p: |- ( ( ph /\ ( x e. W /\ y e. W ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume lbspropd.s1: |- ( ( ph /\ ( x e. P /\ y e. B ) ) -> ( x ( .s ` K ) y ) e. W )
  assume lbspropd.s2: |- ( ( ph /\ ( x e. P /\ y e. B ) ) -> ( x ( .s ` K ) y ) = ( x ( .s ` L ) y ) )
  assume lbspropd.f: |- F = ( Scalar ` K )
  assume lbspropd.g: |- G = ( Scalar ` L )
  assume lbspropd.p1: |- ( ph -> P = ( Base ` F ) )
  assume lbspropd.p2: |- ( ph -> P = ( Base ` G ) )
  assume lbspropd.a: |- ( ( ph /\ ( x e. P /\ y e. P ) ) -> ( x ( +g ` F ) y ) = ( x ( +g ` G ) y ) )
  assume lbspropd.v1: |- ( ph -> K e. _V )
  assume lbspropd.v2: |- ( ph -> L e. _V )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint P x
  disjoint P y
  disjoint W x
  disjoint W y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint u z
  disjoint K u
  disjoint v z
  disjoint K v
  disjoint x z
  disjoint y z
  disjoint K z
  disjoint L u
  disjoint L v
  disjoint L z
  disjoint ph u
  disjoint ph v
  disjoint ph z
  disjoint F u
  disjoint F v
  disjoint G u
  disjoint G v
  disjoint P v
  assert |- ( ph -> ( LBasis ` K ) = ( LBasis ` L ) )

  proof
    wph
    vz
    cK
    clbs
    cfv
    #
    cL
    clbs
    cfv
    #
    wph
    vz
    cv
    #
    cK
    cbs
    cfv
    #
    wss
    #
    @2
    cK
    clspn
    cfv
    #
    cfv
    #
    @3
    wceq
    #
    vv
    cv
    #
    vu
    cv
    #
    cK
    cvsca
    cfv
    #
    co
    #
    @2
    @9
    csn
    cdif
    #
    @5
    cfv
    #
    wcel
    #
    wn
    #
    vv
    cF
    cbs
    cfv
    #
    cF
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    vu
    @2
    wral
    #
    w3a
    #
    @2
    cL
    cbs
    cfv
    #
    wss
    #
    @2
    cL
    clspn
    cfv
    #
    cfv
    #
    @23
    wceq
    #
    @8
    @9
    cL
    cvsca
    cfv
    #
    co
    #
    @12
    @25
    cfv
    #
    wcel
    #
    wn
    #
    vv
    cG
    cbs
    cfv
    #
    cG
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    vu
    @2
    wral
    #
    w3a
    #
    @2
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wph
    @4
    @7
    @21
    wa
    #
    wa
    #
    @24
    @27
    @38
    wa
    #
    wa
    #
    @22
    @39
    wph
    @2
    cB
    wss
    #
    @42
    wa
    @46
    @7
    @38
    wa
    #
    wa
    @43
    @45
    wph
    @46
    @42
    @47
    wph
    @46
    wa
    #
    @21
    @38
    @7
    @48
    @20
    @37
    vu
    @2
    @48
    @9
    @2
    wcel
    #
    wa
    #
    @15
    vv
    cP
    @18
    cdif
    #
    wral
    @32
    vv
    @51
    wral
    @20
    @37
    @50
    @15
    @32
    vv
    @51
    @50
    @8
    @51
    wcel
    #
    wa
    #
    @14
    @31
    @53
    @11
    @29
    @13
    @30
    @53
    wph
    @8
    cP
    wcel
    #
    @9
    cB
    wcel
    #
    @11
    @29
    wceq
    wph
    @46
    @49
    @52
    simplll
    #
    @52
    @54
    @50
    @8
    cP
    @18
    eldifi
    adantl
    @50
    @55
    @52
    @48
    @2
    cB
    @9
    wph
    @46
    simpr
    sselda
    adantr
    wph
    vx
    vy
    cP
    cB
    @10
    @28
    @8
    @9
    lbspropd.s2
    oveqrspc2v
    syl12anc
    @53
    @12
    @5
    @25
    @53
    wph
    @5
    @25
    wceq
    @56
    wph
    vx
    vy
    cB
    cP
    cK
    cL
    cW
    lbspropd.b1
    lbspropd.b2
    lbspropd.w
    lbspropd.p
    lbspropd.s1
    lbspropd.s2
    wph
    cP
    @16
    cK
    csca
    cfv
    #
    cbs
    cfv
    lbspropd.p1
    cF
    @57
    cbs
    lbspropd.f
    fveq2i
    syl6eq
    wph
    cP
    @33
    cL
    csca
    cfv
    #
    cbs
    cfv
    lbspropd.p2
    cG
    @58
    cbs
    lbspropd.g
    fveq2i
    syl6eq
    lbspropd.v1
    lbspropd.v2
    lsppropd
    #
    syl
    fveq1d
    eleq12d
    notbid
    ralbidva
    @50
    @15
    vv
    @51
    @19
    @50
    cP
    @16
    @18
    wph
    cP
    @16
    wceq
    @46
    @49
    lbspropd.p1
    ad2antrr
    difeq1d
    raleqdv
    @50
    @32
    vv
    @51
    @36
    @50
    cP
    @33
    @18
    @35
    wph
    cP
    @33
    wceq
    @46
    @49
    lbspropd.p2
    ad2antrr
    @50
    @17
    @34
    wph
    @17
    @34
    wceq
    @46
    @49
    wph
    vx
    vy
    cP
    cF
    cG
    lbspropd.p1
    lbspropd.p2
    lbspropd.a
    grpidpropd
    ad2antrr
    sneqd
    difeq12d
    raleqdv
    3bitr3d
    ralbidva
    anbi2d
    pm5.32da
    wph
    @46
    @4
    @42
    wph
    cB
    @3
    @2
    lbspropd.b1
    sseq2d
    anbi1d
    wph
    @46
    @24
    @47
    @44
    wph
    cB
    @23
    @2
    lbspropd.b2
    sseq2d
    wph
    @7
    @27
    @38
    wph
    @6
    @26
    @3
    @23
    wph
    @2
    @5
    @25
    @59
    fveq1d
    wph
    cB
    @3
    @23
    lbspropd.b1
    lbspropd.b2
    eqtr3d
    eqeq12d
    anbi1d
    anbi12d
    3bitr3d
    @4
    @7
    @21
    3anass
    @24
    @27
    @38
    3anass
    3bitr4g
    wph
    cK
    cvv
    wcel
    @40
    @22
    wb
    lbspropd.v1
    vu
    vv
    @2
    @10
    cF
    @0
    @16
    @5
    @3
    cK
    cvv
    @17
    @3
    eqid
    lbspropd.f
    @10
    eqid
    @16
    eqid
    @0
    eqid
    @5
    eqid
    @17
    eqid
    islbs
    syl
    wph
    cL
    cvv
    wcel
    @41
    @39
    wb
    lbspropd.v2
    vu
    vv
    @2
    @28
    cG
    @1
    @33
    @25
    @23
    cL
    cvv
    @34
    @23
    eqid
    lbspropd.g
    @28
    eqid
    @33
    eqid
    @1
    eqid
    @25
    eqid
    @34
    eqid
    islbs
    syl
    3bitr4d
    eqrdv
end
