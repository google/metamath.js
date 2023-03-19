include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "wcel.mm"
include "wral.mm"
include "csca.mm"
include "wceq.mm"
include "wa.mm"
include "crab.mm"
include "ssrab2.mm"
include "a1i.mm"
include "clmod.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "ldualvbase.mm"
include "3sstr4d.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "lfl0f.mm"
include "syl.mm"
include "dochoc1.mm"
include "eqidd.mm"
include "wb.mm"
include "lkr0f.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "chlt.mm"
include "doch1.mm"
include "eqtrd.mm"
include "lss0ss.mm"
include "eqsstrd.mm"
include "lcfls1lem.mm"
include "syl3anbrc.mm"
include "ne0i.mm"
include "w3a.mm"
include "adantr.mm"
include "simpr3.mm"
include "simpr2.mm"
include "simpr1.mm"
include "ldualsbase.mm"
include "eleqtrd.mm"
include "lclkrslem1.mm"
include "lclkrslem2.mm"
include "ralrimivvva.mm"
include "islss.mm"

theorem lclkrs
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume lclkrs.h: |- H = ( LHyp ` K )
  assume lclkrs.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrs.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrs.s: |- S = ( LSubSp ` U )
  assume lclkrs.f: |- F = ( LFnl ` U )
  assume lclkrs.l: |- L = ( LKer ` U )
  assume lclkrs.d: |- D = ( LDual ` U )
  assume lclkrs.t: |- T = ( LSubSp ` D )
  assume lclkrs.c: |- C = { f e. F | ( ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) /\ ( ._|_ ` ( L ` f ) ) C_ R ) }
  assume lclkrs.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrs.r: |- ( ph -> R e. S )

  disjoint D f
  disjoint F f
  disjoint L f
  disjoint R f
  disjoint U f
  disjoint ._|_ f
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint D a
  disjoint b f
  disjoint b x
  disjoint D b
  disjoint f x
  disjoint D x
  disjoint a ph
  disjoint b ph
  disjoint ph x
  disjoint C a
  disjoint C b
  disjoint C x
  assert |- ( ph -> C e. T )

  proof
    wph
    cC
    cD
    cbs
    cfv
    #
    wss
    cC
    c0
    wne
    #
    vx
    cv
    #
    va
    cv
    #
    cD
    cvsca
    cfv
    #
    co
    #
    vb
    cv
    #
    cD
    cplusg
    cfv
    #
    co
    cC
    wcel
    #
    vb
    cC
    wral
    va
    cC
    wral
    vx
    cD
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    cC
    cT
    wcel
    wph
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    @11
    wceq
    @12
    cR
    wss
    wa
    #
    vf
    cF
    crab
    #
    cF
    cC
    @0
    @14
    cF
    wss
    wph
    @13
    vf
    cF
    ssrab2
    a1i
    cC
    @14
    wceq
    wph
    lclkrs.c
    a1i
    wph
    cD
    cF
    @0
    cU
    clmod
    lclkrs.f
    lclkrs.d
    @0
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    lclkrs.h
    lclkrs.u
    lclkrs.k
    dvhlmod
    #
    ldualvbase
    3sstr4d
    wph
    cU
    cbs
    cfv
    #
    cU
    csca
    cfv
    #
    c0g
    cfv
    #
    csn
    cxp
    #
    cC
    wcel
    #
    @1
    wph
    @20
    cF
    wcel
    #
    @20
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @23
    wceq
    @24
    cR
    wss
    @21
    wph
    cU
    clmod
    wcel
    #
    @22
    @16
    @18
    cF
    @17
    cU
    @19
    @18
    eqid
    #
    @19
    eqid
    #
    @17
    eqid
    #
    lclkrs.f
    lfl0f
    syl
    #
    wph
    @17
    c.pe
    cfv
    #
    c.pe
    cfv
    @17
    @25
    @23
    wph
    cU
    cH
    cK
    c.pe
    @17
    cW
    lclkrs.h
    lclkrs.u
    lclkrs.o
    @29
    lclkrs.k
    dochoc1
    wph
    @24
    @31
    c.pe
    wph
    @23
    @17
    c.pe
    wph
    @23
    @17
    wceq
    #
    @20
    @20
    wceq
    #
    wph
    @20
    eqidd
    wph
    @26
    @22
    @32
    @33
    wb
    @16
    @30
    @18
    cF
    @20
    cL
    @17
    cU
    @19
    @27
    @28
    @29
    lclkrs.f
    lclkrs.l
    lkr0f
    syl2anc
    mpbird
    #
    fveq2d
    #
    fveq2d
    @34
    3eqtr4d
    wph
    @24
    cU
    c0g
    cfv
    #
    csn
    #
    cR
    wph
    @24
    @31
    @37
    @35
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @31
    @37
    wceq
    lclkrs.k
    cU
    cH
    cK
    c.pe
    @17
    cW
    @36
    lclkrs.h
    lclkrs.u
    lclkrs.o
    @29
    @36
    eqid
    #
    doch1
    syl
    eqtrd
    wph
    @26
    cR
    cS
    wcel
    #
    @37
    cR
    wss
    @16
    lclkrs.r
    cS
    cU
    cR
    @36
    @39
    lclkrs.s
    lss0ss
    syl2anc
    eqsstrd
    cC
    cR
    vf
    cF
    @20
    cL
    c.pe
    lclkrs.c
    lcfls1lem
    syl3anbrc
    cC
    @20
    ne0i
    syl
    wph
    @8
    vx
    va
    vb
    @10
    cC
    cC
    wph
    @2
    @10
    wcel
    #
    @3
    cC
    wcel
    #
    @6
    cC
    wcel
    #
    w3a
    #
    wa
    #
    @18
    cbs
    cfv
    #
    cC
    cD
    @7
    cR
    @18
    cS
    @4
    cU
    vf
    @5
    cF
    @6
    cH
    cK
    cL
    c.pe
    cW
    lclkrs.h
    lclkrs.o
    lclkrs.u
    lclkrs.s
    lclkrs.f
    lclkrs.l
    lclkrs.d
    @27
    @46
    eqid
    #
    @4
    eqid
    #
    lclkrs.c
    wph
    @38
    @44
    lclkrs.k
    adantr
    #
    wph
    @40
    @44
    lclkrs.r
    adantr
    #
    wph
    @41
    @42
    @43
    simpr3
    @7
    eqid
    #
    @45
    @46
    cC
    cD
    cR
    @18
    cS
    @4
    cU
    vf
    cF
    @3
    cH
    cK
    cL
    c.pe
    cW
    @2
    lclkrs.h
    lclkrs.o
    lclkrs.u
    lclkrs.s
    lclkrs.f
    lclkrs.l
    lclkrs.d
    @27
    @47
    @48
    lclkrs.c
    @49
    @50
    wph
    @41
    @42
    @43
    simpr2
    @45
    @2
    @10
    @46
    wph
    @41
    @42
    @43
    simpr1
    wph
    @10
    @46
    wceq
    @44
    wph
    cD
    @9
    @18
    @10
    @46
    clmod
    cU
    @27
    @47
    lclkrs.d
    @9
    eqid
    #
    @10
    eqid
    #
    @16
    ldualsbase
    adantr
    eleqtrd
    lclkrslem1
    lclkrslem2
    ralrimivvva
    vx
    @10
    @7
    cT
    @4
    cC
    @9
    @0
    cD
    va
    vb
    @52
    @53
    @15
    @51
    @48
    lclkrs.t
    islss
    syl3anbrc
end
