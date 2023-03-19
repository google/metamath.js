include "wfn.mm"
include "crn.mm"
include "cpw.mm"
include "cin.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1o.mm"
include "wss.mm"
include "wa.mm"
include "crab.mm"
include "cmpt.mm"
include "clfn.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "chlt.mm"
include "wcel.mm"
include "mapdfval.mm"
include "syl.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "wrex.mm"
include "wb.mm"
include "fvelrnb.mm"
include "adantr.mm"
include "simpr.mm"
include "mapdval.mm"
include "lclkrs2.mm"
include "elin.mm"
include "elpw.mm"
include "anbi2i.mm"
include "bitr2i.mm"
include "sylib.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "ciun.mm"
include "inss1.mm"
include "sseli.mm"
include "adantl.mm"
include "inss2.mm"
include "elpwid.mm"
include "lcfr.mm"
include "mapdrval.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "impbid.mm"
include "bitrd.mm"
include "eqrdv.mm"
include "simprl.mm"
include "simprr.mm"
include "mapd11.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "dff1o6.mm"
include "syl3anbrc.mm"

theorem mapd1o
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cW: class W
  let vc: setvar c
  let vf: setvar f
  let vt: setvar t
  let vu: setvar u
  assume mapd1o.h: |- H = ( LHyp ` K )
  assume mapd1o.o: |- O = ( ( ocH ` K ) ` W )
  assume mapd1o.m: |- M = ( ( mapd ` K ) ` W )
  assume mapd1o.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapd1o.s: |- S = ( LSubSp ` U )
  assume mapd1o.f: |- F = ( LFnl ` U )
  assume mapd1o.l: |- L = ( LKer ` U )
  assume mapd1o.d: |- D = ( LDual ` U )
  assume mapd1o.t: |- T = ( LSubSp ` D )
  assume mapd1o.c: |- C = { g e. F | ( O ` ( O ` ( L ` g ) ) ) = ( L ` g ) }
  assume mapd1o.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint F g
  disjoint K g
  disjoint L g
  disjoint O g
  disjoint U g
  disjoint W g
  disjoint c f
  disjoint c t
  disjoint C c
  disjoint f t
  disjoint C f
  disjoint C t
  disjoint D f
  disjoint f g
  disjoint F f
  disjoint K f
  disjoint g t
  disjoint K t
  disjoint c g
  disjoint L c
  disjoint L f
  disjoint c u
  disjoint M c
  disjoint t u
  disjoint M t
  disjoint M u
  disjoint O c
  disjoint O f
  disjoint S c
  disjoint S t
  disjoint S u
  disjoint T c
  disjoint T f
  disjoint T t
  disjoint U f
  disjoint W f
  disjoint W t
  disjoint c ph
  disjoint f u
  disjoint f ph
  disjoint ph t
  disjoint ph u
  assert |- ( ph -> M : S -1-1-onto-> ( T i^i ~P C ) )

  proof
    wph
    cM
    cS
    wfn
    #
    cM
    crn
    #
    cT
    cC
    cpw
    #
    cin
    #
    wceq
    vt
    cv
    #
    cM
    cfv
    vu
    cv
    #
    cM
    cfv
    wceq
    #
    vt
    vu
    weq
    #
    wi
    #
    vu
    cS
    wral
    vt
    cS
    wral
    cS
    @3
    cM
    wf1o
    wph
    @0
    vt
    cS
    vf
    cv
    cL
    cfv
    #
    cO
    cfv
    #
    cO
    cfv
    @9
    wceq
    #
    @10
    @4
    wss
    wa
    #
    vf
    cF
    crab
    #
    cmpt
    #
    cS
    wfn
    vt
    cS
    @13
    @14
    @12
    vf
    cF
    cF
    cU
    clfn
    cfv
    cvv
    mapd1o.f
    cU
    clfn
    fvex
    eqeltri
    #
    rabex
    @14
    eqid
    fnmpti
    wph
    cS
    cM
    @14
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cM
    @14
    wceq
    mapd1o.k
    cS
    cU
    vf
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    chlt
    vt
    mapd1o.h
    mapd1o.u
    mapd1o.s
    mapd1o.f
    mapd1o.l
    mapd1o.o
    mapd1o.m
    mapdfval
    syl
    fneq1d
    mpbiri
    wph
    vt
    @1
    @3
    wph
    @4
    @1
    wcel
    #
    vc
    cv
    #
    cM
    cfv
    #
    @4
    wceq
    #
    vc
    cS
    wrex
    #
    @4
    @3
    wcel
    #
    wph
    @0
    @17
    @21
    wb
    wph
    @0
    vt
    cS
    vg
    cv
    cL
    cfv
    #
    cO
    cfv
    #
    cO
    cfv
    @23
    wceq
    @24
    @4
    wss
    wa
    #
    vg
    cF
    crab
    #
    cmpt
    #
    cS
    wfn
    vt
    cS
    @26
    @27
    @25
    vg
    cF
    @15
    rabex
    @27
    eqid
    fnmpti
    wph
    cS
    cM
    @27
    wph
    @16
    cM
    @27
    wceq
    mapd1o.k
    cS
    cU
    vg
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    chlt
    vt
    mapd1o.h
    mapd1o.u
    mapd1o.s
    mapd1o.f
    mapd1o.l
    mapd1o.o
    mapd1o.m
    mapdfval
    syl
    fneq1d
    mpbiri
    vc
    cS
    @4
    cM
    fvelrnb
    syl
    wph
    @21
    @22
    wph
    @20
    @22
    vc
    cS
    wph
    @18
    cS
    wcel
    #
    wa
    #
    @19
    @3
    wcel
    @20
    @22
    @29
    @19
    @11
    @10
    @18
    wss
    wa
    #
    vf
    cF
    crab
    #
    @3
    @29
    cS
    @18
    cU
    vf
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    chlt
    mapd1o.h
    mapd1o.u
    mapd1o.s
    mapd1o.f
    mapd1o.l
    mapd1o.o
    mapd1o.m
    wph
    @16
    @28
    mapd1o.k
    adantr
    #
    wph
    @28
    simpr
    #
    mapdval
    @29
    @31
    cT
    wcel
    #
    @31
    cC
    wss
    #
    wa
    #
    @31
    @3
    wcel
    #
    @29
    cC
    cD
    @18
    @31
    cS
    cT
    cU
    vg
    vf
    cF
    cH
    cK
    cL
    cO
    cW
    mapd1o.h
    mapd1o.o
    mapd1o.u
    mapd1o.s
    mapd1o.f
    mapd1o.l
    mapd1o.d
    mapd1o.t
    mapd1o.c
    @31
    eqid
    @32
    @33
    lclkrs2
    @37
    @34
    @31
    @2
    wcel
    #
    wa
    @36
    @31
    cT
    @2
    elin
    @38
    @35
    @34
    @31
    cC
    @30
    vf
    cF
    @15
    rabex
    elpw
    anbi2i
    bitr2i
    sylib
    eqeltrd
    @19
    @4
    @3
    eleq1
    syl5ibcom
    rexlimdva
    wph
    @22
    @21
    wph
    @22
    wa
    #
    vf
    @4
    @10
    ciun
    #
    cS
    wcel
    @40
    cM
    cfv
    #
    @4
    wceq
    #
    @21
    @39
    cC
    cD
    @40
    @4
    cS
    cT
    cU
    vg
    vf
    cF
    cH
    cK
    cL
    cO
    cW
    mapd1o.h
    mapd1o.o
    mapd1o.u
    mapd1o.s
    mapd1o.f
    mapd1o.l
    mapd1o.d
    mapd1o.t
    mapd1o.c
    @40
    eqid
    #
    wph
    @16
    @22
    mapd1o.k
    adantr
    #
    @22
    @4
    cT
    wcel
    wph
    @3
    cT
    @4
    cT
    @2
    inss1
    sseli
    adantl
    #
    @22
    @4
    cC
    wss
    wph
    @22
    @4
    cC
    @3
    @2
    @4
    cT
    @2
    inss2
    sseli
    elpwid
    adantl
    #
    lcfr
    @39
    cC
    cD
    @40
    @4
    cS
    cT
    cU
    vg
    vf
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    mapd1o.h
    mapd1o.o
    mapd1o.m
    mapd1o.u
    mapd1o.s
    mapd1o.f
    mapd1o.l
    mapd1o.d
    mapd1o.t
    mapd1o.c
    @44
    @45
    @46
    @43
    mapdrval
    @20
    @42
    vc
    @40
    cS
    @18
    @40
    wceq
    @19
    @41
    @4
    @18
    @40
    cM
    fveq2
    eqeq1d
    rspcev
    syl2anc
    ex
    impbid
    bitrd
    eqrdv
    wph
    @8
    vt
    vu
    cS
    cS
    wph
    @4
    cS
    wcel
    #
    @5
    cS
    wcel
    #
    wa
    #
    wa
    #
    @6
    @7
    @50
    cS
    cU
    cH
    cK
    cM
    cW
    @4
    @5
    mapd1o.h
    mapd1o.u
    mapd1o.s
    mapd1o.m
    wph
    @16
    @49
    mapd1o.k
    adantr
    wph
    @47
    @48
    simprl
    wph
    @47
    @48
    simprr
    mapd11
    biimpd
    ralrimivva
    vt
    vu
    cS
    @3
    cM
    dff1o6
    syl3anbrc
end
