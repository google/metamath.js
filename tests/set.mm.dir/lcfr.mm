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
include "ciun.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "cbviunv.mm"
include "eqtri.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lssss.mm"
include "syl.mm"
include "ldualvbase.mm"
include "sseqtrd.mm"
include "sselda.mm"
include "lkrssv.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl5eqss.mm"
include "wceq.mm"
include "a1i.mm"
include "c0g.mm"
include "wrex.mm"
include "lduallmod.mm"
include "lss0cl.mm"
include "ldual0vcl.mm"
include "dochlss.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "eliun.mm"
include "ne0i.mm"
include "eqnetrd.mm"
include "w3a.mm"
include "crab.mm"
include "clfn.mm"
include "rabeq.mm"
include "ax-mp.mm"
include "simpr2.mm"
include "simpr1.mm"
include "lcfrlem5.mm"
include "simpr3.mm"
include "lcfrlem42.mm"
include "ralrimivvva.mm"
include "islss.mm"
include "syl3anbrc.mm"

theorem lcfr
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let vh: setvar h
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume lcfr.h: |- H = ( LHyp ` K )
  assume lcfr.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfr.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfr.s: |- S = ( LSubSp ` U )
  assume lcfr.f: |- F = ( LFnl ` U )
  assume lcfr.l: |- L = ( LKer ` U )
  assume lcfr.d: |- D = ( LDual ` U )
  assume lcfr.t: |- T = ( LSubSp ` D )
  assume lcfr.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcfr.q: |- Q = U_ g e. R ( ._|_ ` ( L ` g ) )
  assume lcfr.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfr.r: |- ( ph -> R e. T )
  assume lcfr.rs: |- ( ph -> R C_ C )

  disjoint F f
  disjoint f g
  disjoint L f
  disjoint L g
  disjoint ._|_ f
  disjoint ._|_ g
  disjoint R g
  disjoint U f
  disjoint D h
  disjoint f h
  disjoint g h
  disjoint L h
  disjoint ._|_ h
  disjoint a b
  disjoint a h
  disjoint a x
  disjoint Q a
  disjoint b h
  disjoint b x
  disjoint Q b
  disjoint h x
  disjoint Q h
  disjoint Q x
  disjoint R h
  disjoint a f
  disjoint U a
  disjoint b f
  disjoint U b
  disjoint f x
  disjoint U h
  disjoint U x
  disjoint a ph
  disjoint b ph
  disjoint h ph
  disjoint ph x
  assert |- ( ph -> Q e. S )

  proof
    wph
    cQ
    cU
    cbs
    cfv
    #
    wss
    cQ
    c0
    wne
    vx
    cv
    #
    va
    cv
    #
    cU
    cvsca
    cfv
    #
    co
    #
    vb
    cv
    #
    cU
    cplusg
    cfv
    #
    co
    cQ
    wcel
    #
    vb
    cQ
    wral
    va
    cQ
    wral
    vx
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    cQ
    cS
    wcel
    wph
    cQ
    vh
    cR
    vh
    cv
    #
    cL
    cfv
    #
    c.pe
    cfv
    #
    ciun
    #
    @0
    cQ
    vg
    cR
    vg
    cv
    #
    cL
    cfv
    #
    c.pe
    cfv
    #
    ciun
    @13
    lcfr.q
    vg
    vh
    cR
    @16
    @12
    vg
    vh
    weq
    @15
    @11
    c.pe
    @14
    @10
    cL
    fveq2
    fveq2d
    cbviunv
    eqtri
    #
    wph
    @12
    @0
    wss
    #
    vh
    cR
    wral
    @13
    @0
    wss
    wph
    @18
    vh
    cR
    wph
    @10
    cR
    wcel
    #
    wa
    #
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @11
    @0
    wss
    @18
    wph
    @21
    @19
    lcfr.k
    adantr
    @20
    cF
    @10
    cL
    @0
    cU
    @0
    eqid
    #
    lcfr.f
    lcfr.l
    wph
    cU
    clmod
    wcel
    #
    @19
    wph
    cU
    cH
    cK
    cW
    lcfr.h
    lcfr.u
    lcfr.k
    dvhlmod
    #
    adantr
    wph
    cR
    cF
    @10
    wph
    cR
    cD
    cbs
    cfv
    #
    cF
    wph
    cR
    cT
    wcel
    #
    cR
    @25
    wss
    lcfr.r
    cT
    cR
    @25
    cD
    @25
    eqid
    #
    lcfr.t
    lssss
    syl
    wph
    cD
    cF
    @25
    cU
    clmod
    lcfr.f
    lcfr.d
    @27
    @24
    ldualvbase
    sseqtrd
    sselda
    lkrssv
    cU
    cH
    cK
    c.pe
    @0
    cW
    @11
    lcfr.h
    lcfr.u
    @22
    lcfr.o
    dochssv
    syl2anc
    ralrimiva
    vh
    cR
    @12
    @0
    iunss
    sylibr
    syl5eqss
    wph
    cQ
    @13
    c0
    cQ
    @13
    wceq
    wph
    @17
    a1i
    wph
    cU
    c0g
    cfv
    #
    @13
    wcel
    #
    @13
    c0
    wne
    wph
    @28
    @12
    wcel
    #
    vh
    cR
    wrex
    #
    @29
    wph
    cD
    c0g
    cfv
    #
    cR
    wcel
    #
    @28
    @32
    cL
    cfv
    #
    c.pe
    cfv
    #
    wcel
    #
    @31
    wph
    cD
    clmod
    wcel
    @26
    @33
    wph
    cD
    cU
    lcfr.d
    @24
    lduallmod
    lcfr.r
    cT
    cR
    cD
    @32
    @32
    eqid
    #
    lcfr.t
    lss0cl
    syl2anc
    wph
    @23
    @35
    cS
    wcel
    #
    @36
    @24
    wph
    @21
    @34
    @0
    wss
    @38
    lcfr.k
    wph
    cF
    @32
    cL
    @0
    cU
    @22
    lcfr.f
    lcfr.l
    @24
    wph
    cD
    cF
    cU
    @32
    lcfr.f
    lcfr.d
    @37
    @24
    ldual0vcl
    lkrssv
    cS
    cU
    cH
    cK
    c.pe
    @0
    cW
    @34
    lcfr.h
    lcfr.u
    @22
    lcfr.s
    lcfr.o
    dochlss
    syl2anc
    cS
    @35
    cU
    @28
    @28
    eqid
    lcfr.s
    lss0cl
    syl2anc
    @30
    @36
    vh
    @32
    cR
    @10
    @32
    wceq
    #
    @12
    @35
    @28
    @39
    @11
    @34
    c.pe
    @10
    @32
    cL
    fveq2
    fveq2d
    eleq2d
    rspcev
    syl2anc
    vh
    @28
    cR
    @12
    eliun
    sylibr
    @13
    @28
    ne0i
    syl
    eqnetrd
    wph
    @7
    vx
    va
    vb
    @9
    cQ
    cQ
    wph
    @1
    @9
    wcel
    #
    @2
    cQ
    wcel
    #
    @5
    cQ
    wcel
    #
    w3a
    #
    wa
    #
    cC
    cD
    @6
    cT
    cU
    vf
    vh
    cQ
    cF
    cR
    cH
    cK
    cL
    c.pe
    cW
    @4
    @5
    lcfr.h
    lcfr.o
    lcfr.u
    @6
    eqid
    #
    lcfr.f
    lcfr.l
    lcfr.d
    lcfr.t
    cC
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @46
    wceq
    #
    vf
    cF
    crab
    #
    @47
    vf
    cU
    clfn
    cfv
    #
    crab
    #
    lcfr.c
    cF
    @49
    wceq
    @48
    @50
    wceq
    lcfr.f
    @47
    vf
    cF
    @49
    rabeq
    ax-mp
    eqtri
    @17
    wph
    @21
    @43
    lcfr.k
    adantr
    #
    wph
    @26
    @43
    lcfr.r
    adantr
    #
    wph
    cR
    cC
    wss
    @43
    lcfr.rs
    adantr
    @44
    @1
    @9
    @8
    cD
    cQ
    cR
    cT
    @3
    cU
    vh
    cF
    cH
    cK
    cL
    c.pe
    @0
    cW
    @2
    lcfr.h
    lcfr.o
    lcfr.u
    @22
    lcfr.f
    lcfr.l
    lcfr.d
    lcfr.t
    @51
    @52
    @17
    wph
    @40
    @41
    @42
    simpr2
    @8
    eqid
    #
    @9
    eqid
    #
    @3
    eqid
    #
    wph
    @40
    @41
    @42
    simpr1
    lcfrlem5
    wph
    @40
    @41
    @42
    simpr3
    lcfrlem42
    ralrimivvva
    vx
    @9
    @6
    cS
    @3
    cQ
    @8
    @0
    cU
    va
    vb
    @53
    @54
    @22
    @45
    @55
    lcfr.s
    islss
    syl3anbrc
end
