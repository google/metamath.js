include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "crab.mm"
include "chlt.mm"
include "mapdvalc.mm"
include "sseq12d.mm"
include "wi.mm"
include "wral.mm"
include "ss2rab.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "eqid.mm"
include "mapdordlem1a.mm"
include "simprl.mm"
include "idd.mm"
include "embantd.mm"
include "ex.mm"
include "sylbid.mm"
include "com23.mm"
include "ralimdv2.mm"
include "syl5bi.mm"
include "dvhlmod.mm"
include "lssatle.mm"
include "wceq.mm"
include "mapdordlem1.mm"
include "simprbi.mm"
include "adantl.mm"
include "adantr.mm"
include "simplbi.mm"
include "dochlkr.mm"
include "mpbid.mm"
include "simpld.mm"
include "simprd.mm"
include "dochshpsat.mm"
include "wex.mm"
include "wrex.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "simpr.mm"
include "dochsatshp.mm"
include "lshpkrex.mm"
include "syl2anc.mm"
include "df-rex.mm"
include "sylib.mm"
include "simprr.mm"
include "fveq2d.mm"
include "cdih.mm"
include "crn.mm"
include "clmod.mm"
include "lsatssv.mm"
include "dochcl.mm"
include "dochoc.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "sylanbrc.mm"
include "dih1dimat.mm"
include "eqtr2d.mm"
include "jca.mm"
include "eximdv.mm"
include "mpd.mm"
include "sylibr.mm"
include "wb.mm"
include "sseq1.mm"
include "imbi12d.mm"
include "ralxfrd.mm"
include "bitr2d.mm"
include "sylibd.mm"
include "simplr.mm"
include "sstr.mm"
include "ancoms.mm"
include "a1i.mm"
include "mpand.mm"
include "ss2rabdv.mm"
include "impbid.mm"
include "bitrd.mm"

theorem mapdordlem2
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vp: setvar p
  assume mapdord.h: |- H = ( LHyp ` K )
  assume mapdord.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdord.s: |- S = ( LSubSp ` U )
  assume mapdord.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdord.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdord.x: |- ( ph -> X e. S )
  assume mapdord.y: |- ( ph -> Y e. S )
  assume mapdord.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdord.a: |- A = ( LSAtoms ` U )
  assume mapdord.f: |- F = ( LFnl ` U )
  assume mapdord.c: |- J = ( LSHyp ` U )
  assume mapdord.l: |- L = ( LKer ` U )
  assume mapdord.t: |- T = { g e. F | ( O ` ( O ` ( L ` g ) ) ) e. J }
  assume mapdord.q: |- C = { g e. F | ( O ` ( O ` ( L ` g ) ) ) = ( L ` g ) }

  disjoint F g
  disjoint J g
  disjoint L g
  disjoint O g
  disjoint K g
  disjoint U g
  disjoint W g
  disjoint f p
  disjoint A f
  disjoint A p
  disjoint f g
  disjoint F f
  disjoint L f
  disjoint g p
  disjoint L p
  disjoint O f
  disjoint O p
  disjoint T p
  disjoint X f
  disjoint X p
  disjoint Y f
  disjoint Y p
  disjoint f ph
  disjoint p ph
  disjoint f g
  disjoint K f
  disjoint S p
  disjoint f p
  disjoint U f
  disjoint g p
  disjoint U p
  disjoint W f
  assert |- ( ph -> ( ( M ` X ) C_ ( M ` Y ) <-> X C_ Y ) )

  proof
    wph
    cX
    cM
    cfv
    #
    cY
    cM
    cfv
    #
    wss
    vf
    cv
    #
    cL
    cfv
    #
    cO
    cfv
    #
    cX
    wss
    #
    vf
    cC
    crab
    #
    @4
    cY
    wss
    #
    vf
    cC
    crab
    #
    wss
    #
    cX
    cY
    wss
    #
    wph
    @0
    @6
    @1
    @8
    wph
    cC
    cS
    cX
    cU
    vf
    vg
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    chlt
    mapdord.h
    mapdord.u
    mapdord.s
    mapdord.f
    mapdord.l
    mapdord.o
    mapdord.m
    mapdord.k
    mapdord.x
    mapdord.q
    mapdvalc
    wph
    cC
    cS
    cY
    cU
    vf
    vg
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    chlt
    mapdord.h
    mapdord.u
    mapdord.s
    mapdord.f
    mapdord.l
    mapdord.o
    mapdord.m
    mapdord.k
    mapdord.y
    mapdord.q
    mapdvalc
    sseq12d
    wph
    @9
    @10
    wph
    @9
    @5
    @7
    wi
    #
    vf
    cT
    wral
    #
    @10
    @9
    @11
    vf
    cC
    wral
    wph
    @12
    @5
    @7
    vf
    cC
    ss2rab
    wph
    @11
    @11
    vf
    cC
    cT
    wph
    @2
    cT
    wcel
    #
    @2
    cC
    wcel
    #
    @11
    wi
    #
    @11
    wph
    @13
    @14
    @4
    cO
    cfv
    #
    cJ
    wcel
    #
    wa
    #
    @15
    @11
    wi
    #
    wph
    cC
    cT
    cU
    vg
    cF
    cH
    @2
    cK
    cL
    cO
    cU
    cbs
    cfv
    #
    cW
    cJ
    mapdord.h
    mapdord.o
    mapdord.u
    @20
    eqid
    #
    mapdord.c
    mapdord.f
    mapdord.l
    mapdord.t
    mapdord.q
    mapdord.k
    mapdordlem1a
    wph
    @18
    @19
    wph
    @18
    wa
    #
    @14
    @11
    @11
    wph
    @14
    @17
    simprl
    @22
    @11
    idd
    embantd
    ex
    sylbid
    com23
    ralimdv2
    syl5bi
    wph
    @10
    vp
    cv
    #
    cX
    wss
    #
    @23
    cY
    wss
    #
    wi
    #
    vp
    cA
    wral
    @12
    wph
    cA
    cS
    cX
    cY
    cU
    vp
    mapdord.s
    mapdord.a
    wph
    cU
    cH
    cK
    cW
    mapdord.h
    mapdord.u
    mapdord.k
    dvhlmod
    #
    mapdord.x
    mapdord.y
    lssatle
    wph
    @26
    @11
    vp
    vf
    @4
    cA
    cT
    wph
    @13
    wa
    #
    @16
    @3
    wceq
    #
    @4
    cA
    wcel
    @28
    @29
    @3
    cJ
    wcel
    #
    @28
    @17
    @29
    @30
    wa
    @13
    @17
    wph
    @13
    @2
    cF
    wcel
    #
    @17
    cT
    vg
    cF
    @2
    cL
    cO
    cJ
    mapdord.t
    mapdordlem1
    #
    simprbi
    adantl
    @28
    cU
    cF
    @2
    cH
    cK
    cL
    cO
    cW
    cJ
    mapdord.h
    mapdord.o
    mapdord.u
    mapdord.f
    mapdord.c
    mapdord.l
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @13
    mapdord.k
    adantr
    #
    @13
    @31
    wph
    @13
    @31
    @17
    @32
    simplbi
    adantl
    dochlkr
    mpbid
    #
    simpld
    @28
    cA
    cU
    cH
    cK
    cO
    cW
    @3
    cJ
    mapdord.h
    mapdord.o
    mapdord.u
    mapdord.a
    mapdord.c
    @34
    @28
    @29
    @30
    @35
    simprd
    dochshpsat
    mpbid
    wph
    @23
    cA
    wcel
    #
    wa
    #
    @13
    @23
    @4
    wceq
    #
    wa
    #
    vf
    wex
    #
    @38
    vf
    cT
    wrex
    @37
    @31
    @3
    @23
    cO
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    @40
    @37
    @42
    vf
    cF
    wrex
    #
    @44
    @37
    cU
    clvec
    wcel
    #
    @41
    cJ
    wcel
    #
    @45
    wph
    @46
    @36
    wph
    cU
    cH
    cK
    cW
    mapdord.h
    mapdord.u
    mapdord.k
    dvhlvec
    adantr
    @37
    cA
    @23
    cU
    cH
    cK
    cO
    cW
    cJ
    mapdord.h
    mapdord.u
    mapdord.o
    mapdord.a
    mapdord.c
    wph
    @33
    @36
    mapdord.k
    adantr
    #
    wph
    @36
    simpr
    #
    dochsatshp
    #
    @41
    vf
    cF
    cJ
    cL
    cU
    mapdord.c
    mapdord.f
    mapdord.l
    lshpkrex
    syl2anc
    @42
    vf
    cF
    df-rex
    sylib
    @37
    @43
    @39
    vf
    @37
    @43
    @39
    @37
    @43
    wa
    #
    @13
    @38
    @51
    @31
    @17
    @13
    @37
    @31
    @42
    simprl
    @51
    @16
    @41
    cJ
    @51
    @16
    @41
    cO
    cfv
    #
    cO
    cfv
    #
    @41
    @51
    @4
    @52
    cO
    @51
    @3
    @41
    cO
    @37
    @31
    @42
    simprr
    fveq2d
    #
    fveq2d
    @37
    @53
    @41
    wceq
    #
    @43
    @37
    @33
    @41
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    #
    wcel
    #
    @55
    @48
    @37
    @33
    @23
    @20
    wss
    @58
    @48
    @37
    cA
    @23
    @20
    cU
    @21
    mapdord.a
    wph
    cU
    clmod
    wcel
    @36
    @27
    adantr
    @49
    lsatssv
    cU
    cH
    @56
    cK
    cO
    @20
    cW
    @23
    mapdord.h
    @56
    eqid
    #
    mapdord.u
    @21
    mapdord.o
    dochcl
    syl2anc
    cH
    @56
    cK
    cO
    cW
    @41
    mapdord.h
    @59
    mapdord.o
    dochoc
    syl2anc
    adantr
    eqtrd
    @37
    @47
    @43
    @50
    adantr
    eqeltrd
    @32
    sylanbrc
    @51
    @4
    @52
    @23
    @54
    @37
    @52
    @23
    wceq
    #
    @43
    @37
    @33
    @23
    @57
    wcel
    #
    @60
    @48
    @37
    @33
    @36
    @61
    @48
    @49
    cA
    @23
    cU
    cH
    @56
    cK
    cW
    mapdord.h
    mapdord.u
    @59
    mapdord.a
    dih1dimat
    syl2anc
    cH
    @56
    cK
    cO
    cW
    @23
    mapdord.h
    @59
    mapdord.o
    dochoc
    syl2anc
    adantr
    eqtr2d
    jca
    ex
    eximdv
    mpd
    @38
    vf
    cT
    df-rex
    sylibr
    @38
    @26
    @11
    wb
    wph
    @38
    @24
    @5
    @25
    @7
    @23
    @4
    cX
    sseq1
    @23
    @4
    cY
    sseq1
    imbi12d
    adantl
    ralxfrd
    bitr2d
    sylibd
    wph
    @10
    @9
    wph
    @10
    wa
    #
    @5
    @7
    vf
    cC
    @62
    @14
    wa
    #
    @10
    @5
    @7
    wph
    @10
    @14
    simplr
    @10
    @5
    wa
    @7
    wi
    @63
    @5
    @10
    @7
    @4
    cX
    cY
    sstr
    ancoms
    a1i
    mpand
    ss2rabdv
    ex
    impbid
    bitrd
end
