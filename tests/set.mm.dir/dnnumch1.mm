include "wcel.mm"
include "cv.mm"
include "cima.mm"
include "cdif.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "con0.mm"
include "wral.mm"
include "cres.mm"
include "wf1o.mm"
include "wrex.mm"
include "wa.mm"
include "wceq.mm"
include "cvv.mm"
include "crn.mm"
include "cmpt.mm"
include "crecs.mm"
include "recsval.mm"
include "fveq1i.mm"
include "wfun.mm"
include "wfn.mm"
include "tfr1.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "vex.mm"
include "resfunexg.mm"
include "mp2an.mm"
include "rneq.mm"
include "df-ima.mm"
include "syl6eqr.mm"
include "difeq2d.mm"
include "fveq2d.mm"
include "weq.mm"
include "cbvmptv.mm"
include "fvex.mm"
include "fvmpt.mm"
include "reseq1i.mm"
include "fveq2i.mm"
include "eqtr3i.mm"
include "3eqtr4g.mm"
include "ad2antlr.mm"
include "cpw.mm"
include "wss.mm"
include "difss.mm"
include "wb.mm"
include "elpw2g.mm"
include "syl.mm"
include "mpbiri.mm"
include "neeq1.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "adantr.mm"
include "imp.mm"
include "eqeltrd.mm"
include "ex.mm"
include "ralrimiva.mm"
include "tz7.49c.mm"

theorem dnnumch1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  assume dnnumch.f: |- F = recs ( ( z e. _V |-> ( G ` ( A \ ran z ) ) ) )
  assume dnnumch.a: |- ( ph -> A e. V )
  assume dnnumch.g: |- ( ph -> A. y e. ~P A ( y =/= (/) -> ( G ` y ) e. y ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint ph x
  disjoint F v
  disjoint F w
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint G v
  disjoint G w
  disjoint v z
  disjoint w z
  disjoint A v
  disjoint A w
  disjoint ph v
  disjoint ph w
  assert |- ( ph -> E. x e. On ( F |` x ) : x -1-1-onto-> A )

  proof
    wph
    cA
    cV
    wcel
    #
    cA
    cF
    vx
    cv
    #
    cima
    #
    cdif
    #
    c0
    wne
    #
    @1
    cF
    cfv
    #
    @3
    wcel
    #
    wi
    #
    vx
    con0
    wral
    @1
    cA
    cF
    @1
    cres
    #
    wf1o
    vx
    con0
    wrex
    dnnumch.a
    wph
    @7
    vx
    con0
    wph
    @1
    con0
    wcel
    #
    wa
    #
    @4
    @6
    @10
    @4
    wa
    @5
    @3
    cG
    cfv
    #
    @3
    @9
    @5
    @11
    wceq
    wph
    @4
    @9
    @1
    vz
    cvv
    cA
    vz
    cv
    #
    crn
    #
    cdif
    #
    cG
    cfv
    #
    cmpt
    #
    crecs
    #
    cfv
    @17
    @1
    cres
    #
    @16
    cfv
    #
    @5
    @11
    @1
    @16
    recsval
    @1
    cF
    @17
    dnnumch.f
    fveq1i
    @8
    @16
    cfv
    #
    @11
    @19
    @8
    cvv
    wcel
    #
    @20
    @11
    wceq
    cF
    wfun
    #
    @1
    cvv
    wcel
    @21
    cF
    con0
    wfn
    @22
    cF
    @16
    dnnumch.f
    tfr1
    #
    con0
    cF
    fnfun
    ax-mp
    vx
    vex
    cF
    @1
    cvv
    resfunexg
    mp2an
    vw
    @8
    cA
    vw
    cv
    #
    crn
    #
    cdif
    #
    cG
    cfv
    #
    @11
    cvv
    @16
    @24
    @8
    wceq
    #
    @26
    @3
    cG
    @28
    @25
    @2
    cA
    @28
    @25
    @8
    crn
    @2
    @24
    @8
    rneq
    cF
    @1
    df-ima
    syl6eqr
    difeq2d
    fveq2d
    vz
    vw
    cvv
    @15
    @27
    vz
    vw
    weq
    #
    @14
    @26
    cG
    @29
    @13
    @25
    cA
    @12
    @24
    rneq
    difeq2d
    fveq2d
    cbvmptv
    @3
    cG
    fvex
    fvmpt
    ax-mp
    @8
    @18
    @16
    cF
    @17
    @1
    dnnumch.f
    reseq1i
    fveq2i
    eqtr3i
    3eqtr4g
    ad2antlr
    @10
    @4
    @11
    @3
    wcel
    #
    wph
    @4
    @30
    wi
    #
    @9
    wph
    @3
    cA
    cpw
    #
    wcel
    #
    vy
    cv
    #
    c0
    wne
    #
    @34
    cG
    cfv
    #
    @34
    wcel
    #
    wi
    #
    vy
    @32
    wral
    @31
    wph
    @33
    @3
    cA
    wss
    #
    cA
    @2
    difss
    wph
    @0
    @33
    @39
    wb
    dnnumch.a
    @3
    cA
    cV
    elpw2g
    syl
    mpbiri
    dnnumch.g
    @38
    @31
    vy
    @3
    @32
    @34
    @3
    wceq
    #
    @35
    @4
    @37
    @30
    @34
    @3
    c0
    neeq1
    @40
    @36
    @11
    @34
    @3
    @34
    @3
    cG
    fveq2
    @40
    id
    eleq12d
    imbi12d
    rspcva
    syl2anc
    adantr
    imp
    eqeltrd
    ex
    ralrimiva
    vx
    cA
    cV
    cF
    @23
    tz7.49c
    syl2anc
end
