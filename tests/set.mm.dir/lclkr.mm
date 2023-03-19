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
include "wb.mm"
include "lkr0f.mm"
include "syl2anc.mm"
include "mpbiri.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "lcfl1lem.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "w3a.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "simpr1.mm"
include "ldualsbase.mm"
include "eleqtrd.mm"
include "simpr2.mm"
include "lclkrlem1.mm"
include "simpr3.mm"
include "lclkrlem2.mm"
include "ralrimivvva.mm"
include "islss.mm"
include "syl3anbrc.mm"

theorem lclkr
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
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
  assume lclkr.h: |- H = ( LHyp ` K )
  assume lclkr.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkr.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkr.f: |- F = ( LFnl ` U )
  assume lclkr.l: |- L = ( LKer ` U )
  assume lclkr.d: |- D = ( LDual ` U )
  assume lclkr.s: |- S = ( LSubSp ` D )
  assume lclkr.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lclkr.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint ._|_ f
  disjoint D f
  disjoint F f
  disjoint L f
  disjoint U f
  disjoint a b
  disjoint a x
  disjoint C a
  disjoint b x
  disjoint C b
  disjoint C x
  disjoint a f
  disjoint D a
  disjoint b f
  disjoint D b
  disjoint f x
  disjoint D x
  disjoint a ph
  disjoint b ph
  disjoint ph x
  assert |- ( ph -> C e. S )

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
    cS
    wcel
    wph
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @11
    wceq
    #
    vf
    cF
    crab
    #
    cF
    cC
    @0
    @13
    cF
    wss
    wph
    @12
    vf
    cF
    ssrab2
    a1i
    cC
    @13
    wceq
    wph
    lclkr.c
    a1i
    wph
    cD
    cF
    @0
    cU
    clmod
    lclkr.f
    lclkr.d
    @0
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    lclkr.h
    lclkr.u
    lclkr.k
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
    @19
    cF
    wcel
    #
    @19
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @22
    wceq
    @20
    wph
    cU
    clmod
    wcel
    #
    @21
    @15
    @17
    cF
    @16
    cU
    @18
    @17
    eqid
    #
    @18
    eqid
    #
    @16
    eqid
    #
    lclkr.f
    lfl0f
    syl
    #
    wph
    @16
    c.pe
    cfv
    #
    c.pe
    cfv
    @16
    @24
    @22
    wph
    cU
    cH
    cK
    c.pe
    @16
    cW
    lclkr.h
    lclkr.u
    lclkr.o
    @28
    lclkr.k
    dochoc1
    wph
    @23
    @30
    c.pe
    wph
    @22
    @16
    c.pe
    wph
    @22
    @16
    wceq
    #
    @19
    @19
    wceq
    #
    @19
    eqid
    wph
    @25
    @21
    @31
    @32
    wb
    @15
    @29
    @17
    cF
    @19
    cL
    @16
    cU
    @18
    @26
    @27
    @28
    lclkr.f
    lclkr.l
    lkr0f
    syl2anc
    mpbiri
    #
    fveq2d
    fveq2d
    @33
    3eqtr4d
    cC
    vf
    cF
    @19
    cL
    c.pe
    lclkr.c
    lcfl1lem
    sylanbrc
    cC
    @19
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
    cC
    cD
    @7
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
    lclkr.h
    lclkr.o
    lclkr.u
    lclkr.f
    lclkr.l
    lclkr.d
    @7
    eqid
    #
    lclkr.c
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @37
    lclkr.k
    adantr
    #
    @38
    @17
    cbs
    cfv
    #
    cC
    cD
    @17
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
    lclkr.h
    lclkr.o
    lclkr.u
    lclkr.f
    lclkr.l
    lclkr.d
    @26
    @41
    eqid
    #
    @4
    eqid
    #
    lclkr.c
    @40
    @38
    @2
    @10
    @41
    wph
    @34
    @35
    @36
    simpr1
    wph
    @10
    @41
    wceq
    @37
    wph
    cD
    @9
    @17
    @10
    @41
    clmod
    cU
    @26
    @42
    lclkr.d
    @9
    eqid
    #
    @10
    eqid
    #
    @15
    ldualsbase
    adantr
    eleqtrd
    wph
    @34
    @35
    @36
    simpr2
    lclkrlem1
    wph
    @34
    @35
    @36
    simpr3
    lclkrlem2
    ralrimivvva
    vx
    @10
    @7
    cS
    @4
    cC
    @9
    @0
    cD
    va
    vb
    @44
    @45
    @14
    @39
    @43
    lclkr.s
    islss
    syl3anbrc
end
