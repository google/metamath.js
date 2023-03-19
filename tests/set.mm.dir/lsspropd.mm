include "clss.mm"
include "cfv.mm"
include "cv.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "wcel.mm"
include "wral.mm"
include "csca.mm"
include "w3a.mm"
include "wa.mm"
include "wb.mm"
include "wceq.mm"
include "simpll.mm"
include "simprl.mm"
include "simplr.mm"
include "simprrl.mm"
include "sseldd.mm"
include "ralrimivva.mm"
include "ad2antrr.mm"
include "ovrspc2v.mm"
include "syl21anc.mm"
include "simprrr.mm"
include "oveqrspc2v.mm"
include "syl12anc.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "anassrs.mm"
include "2ralbidva.mm"
include "ralbidva.mm"
include "anbi2d.mm"
include "pm5.32da.mm"
include "3anass.mm"
include "3bitr4g.mm"
include "sseq2d.mm"
include "raleqdv.mm"
include "3anbi13d.mm"
include "3bitr3d.mm"
include "eqid.mm"
include "islss.mm"
include "eqrdv.mm"

theorem lsspropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cP: class P
  let cK: class K
  let cL: class L
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let vs: setvar s
  let vt: setvar t
  assume lsspropd.b1: |- ( ph -> B = ( Base ` K ) )
  assume lsspropd.b2: |- ( ph -> B = ( Base ` L ) )
  assume lsspropd.w: |- ( ph -> B C_ W )
  assume lsspropd.p: |- ( ( ph /\ ( x e. W /\ y e. W ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume lsspropd.s1: |- ( ( ph /\ ( x e. P /\ y e. B ) ) -> ( x ( .s ` K ) y ) e. W )
  assume lsspropd.s2: |- ( ( ph /\ ( x e. P /\ y e. B ) ) -> ( x ( .s ` K ) y ) = ( x ( .s ` L ) y ) )
  assume lsspropd.p1: |- ( ph -> P = ( Base ` ( Scalar ` K ) ) )
  assume lsspropd.p2: |- ( ph -> P = ( Base ` ( Scalar ` L ) ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint W x
  disjoint W y
  disjoint L x
  disjoint L y
  disjoint P x
  disjoint P y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint B a
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint a s
  disjoint a t
  disjoint K a
  disjoint b s
  disjoint b t
  disjoint K b
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint K s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint K t
  disjoint K z
  disjoint a ph
  disjoint b ph
  disjoint ph s
  disjoint ph z
  disjoint L a
  disjoint L b
  disjoint L s
  disjoint L t
  disjoint L z
  disjoint P a
  disjoint P b
  disjoint P z
  assert |- ( ph -> ( LSubSp ` K ) = ( LSubSp ` L ) )

  proof
    wph
    vs
    cK
    clss
    cfv
    #
    cL
    clss
    cfv
    #
    wph
    vs
    cv
    #
    cK
    cbs
    cfv
    #
    wss
    #
    @2
    c0
    wne
    #
    vz
    cv
    #
    va
    cv
    #
    cK
    cvsca
    cfv
    #
    co
    #
    vb
    cv
    #
    cK
    cplusg
    cfv
    #
    co
    #
    @2
    wcel
    #
    vb
    @2
    wral
    va
    @2
    wral
    #
    vz
    cK
    csca
    cfv
    #
    cbs
    cfv
    #
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
    @5
    @6
    @7
    cL
    cvsca
    cfv
    #
    co
    #
    @10
    cL
    cplusg
    cfv
    #
    co
    #
    @2
    wcel
    #
    vb
    @2
    wral
    va
    @2
    wral
    #
    vz
    cL
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    #
    w3a
    #
    @2
    @0
    wcel
    @2
    @1
    wcel
    wph
    @2
    cB
    wss
    #
    @5
    @14
    vz
    cP
    wral
    #
    w3a
    #
    @31
    @5
    @26
    vz
    cP
    wral
    #
    w3a
    #
    @18
    @30
    wph
    @31
    @5
    @32
    wa
    #
    wa
    @31
    @5
    @34
    wa
    #
    wa
    @33
    @35
    wph
    @31
    @36
    @37
    wph
    @31
    wa
    #
    @32
    @34
    @5
    @38
    @14
    @26
    vz
    cP
    @38
    @6
    cP
    wcel
    #
    wa
    @13
    @25
    va
    vb
    @2
    @2
    @38
    @39
    @7
    @2
    wcel
    #
    @10
    @2
    wcel
    #
    wa
    #
    @13
    @25
    wb
    @38
    @39
    @42
    wa
    #
    wa
    #
    @12
    @24
    @2
    @44
    @12
    @9
    @10
    @23
    co
    #
    @24
    @44
    wph
    @9
    cW
    wcel
    #
    @10
    cW
    wcel
    @12
    @45
    wceq
    wph
    @31
    @43
    simpll
    #
    @44
    @39
    @7
    cB
    wcel
    #
    vx
    cv
    vy
    cv
    @8
    co
    cW
    wcel
    #
    vy
    cB
    wral
    vx
    cP
    wral
    #
    @46
    @38
    @39
    @42
    simprl
    #
    @44
    @2
    cB
    @7
    wph
    @31
    @43
    simplr
    #
    @38
    @39
    @40
    @41
    simprrl
    sseldd
    #
    wph
    @50
    @31
    @43
    wph
    @49
    vx
    vy
    cP
    cB
    lsspropd.s1
    ralrimivva
    ad2antrr
    vx
    vy
    cP
    cB
    cW
    @8
    @6
    @7
    ovrspc2v
    syl21anc
    @44
    cB
    cW
    @10
    wph
    cB
    cW
    wss
    @31
    @43
    lsspropd.w
    ad2antrr
    @44
    @2
    cB
    @10
    @52
    @38
    @39
    @40
    @41
    simprrr
    sseldd
    sseldd
    wph
    vx
    vy
    cW
    cW
    @11
    @23
    @9
    @10
    lsspropd.p
    oveqrspc2v
    syl12anc
    @44
    @9
    @22
    @10
    @23
    @44
    wph
    @39
    @48
    @9
    @22
    wceq
    @47
    @51
    @53
    wph
    vx
    vy
    cP
    cB
    @8
    @21
    @6
    @7
    lsspropd.s2
    oveqrspc2v
    syl12anc
    oveq1d
    eqtrd
    eleq1d
    anassrs
    2ralbidva
    ralbidva
    anbi2d
    pm5.32da
    @31
    @5
    @32
    3anass
    @31
    @5
    @34
    3anass
    3bitr4g
    wph
    @31
    @4
    @32
    @17
    @5
    wph
    cB
    @3
    @2
    lsspropd.b1
    sseq2d
    wph
    @14
    vz
    cP
    @16
    lsspropd.p1
    raleqdv
    3anbi13d
    wph
    @31
    @20
    @34
    @29
    @5
    wph
    cB
    @19
    @2
    lsspropd.b2
    sseq2d
    wph
    @26
    vz
    cP
    @28
    lsspropd.p2
    raleqdv
    3anbi13d
    3bitr3d
    vz
    @16
    @11
    @0
    @8
    @2
    @15
    @3
    cK
    va
    vb
    @15
    eqid
    @16
    eqid
    @3
    eqid
    @11
    eqid
    @8
    eqid
    @0
    eqid
    islss
    vz
    @28
    @23
    @1
    @21
    @2
    @27
    @19
    cL
    va
    vb
    @27
    eqid
    @28
    eqid
    @19
    eqid
    @23
    eqid
    @21
    eqid
    @1
    eqid
    islss
    3bitr4g
    eqrdv
end
