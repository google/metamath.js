include "cima.mm"
include "wss.mm"
include "wfun.mm"
include "cdm.mm"
include "cin.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cres.mm"
include "dmres.mm"
include "imaeq2i.mm"
include "imadmres.mm"
include "eqtr3i.mm"
include "sseq2i.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "ssrab2.mm"
include "ssel2.mm"
include "adantll.mm"
include "wi.mm"
include "wrex.mm"
include "fvelima.mm"
include "ex.mm"
include "adantr.mm"
include "eleq1a.mm"
include "anim2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "syl6ibr.mm"
include "simpr.mm"
include "a1i.mm"
include "jcad.mm"
include "reximdv2.mm"
include "adantl.mm"
include "wb.mm"
include "wfn.mm"
include "funfn.mm"
include "inss2.mm"
include "sstri.mm"
include "fvelimab.mm"
include "mpan2.mm"
include "sylbi.mm"
include "sylibrd.mm"
include "syld.mm"
include "adantlr.mm"
include "mpd.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "rexlimiv.mm"
include "syl6.mm"
include "impbid.mm"
include "eqrdv.mm"
include "inex1.mm"
include "rabex.mm"
include "sseq1.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "spcev.mm"
include "sylancr.mm"
include "inss1.mm"
include "sstr.mm"
include "anim1i.mm"
include "eximi.mm"
include "syl.mm"
include "sylan2br.mm"

theorem ssimaex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume ssimaex.1: |- A e. _V

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint F w
  disjoint F y
  disjoint F z
  assert |- ( ( Fun F /\ B C_ ( F " A ) ) -> E. x ( x C_ A /\ B = ( F " x ) ) )

  proof
    cB
    cF
    cA
    cima
    #
    wss
    cF
    wfun
    #
    cB
    cF
    cA
    cF
    cdm
    #
    cin
    #
    cima
    #
    wss
    #
    vx
    cv
    #
    cA
    wss
    #
    cB
    cF
    @6
    cima
    #
    wceq
    #
    wa
    #
    vx
    wex
    #
    @4
    @0
    cB
    cF
    cF
    cA
    cres
    cdm
    #
    cima
    @4
    @0
    @12
    @3
    cF
    cF
    cA
    dmres
    imaeq2i
    cF
    cA
    imadmres
    eqtr3i
    sseq2i
    @1
    @5
    wa
    #
    @6
    @3
    wss
    #
    @9
    wa
    #
    vx
    wex
    #
    @11
    @13
    vy
    cv
    #
    cF
    cfv
    #
    cB
    wcel
    #
    vy
    @3
    crab
    #
    @3
    wss
    #
    cB
    cF
    @20
    cima
    #
    wceq
    #
    @16
    @19
    vy
    @3
    ssrab2
    #
    @13
    vz
    cB
    @22
    @13
    vz
    cv
    #
    cB
    wcel
    #
    @25
    @22
    wcel
    #
    @13
    @26
    @27
    @13
    @26
    wa
    @25
    @4
    wcel
    #
    @27
    @5
    @26
    @28
    @1
    cB
    @4
    @25
    ssel2
    adantll
    @1
    @26
    @28
    @27
    wi
    @5
    @1
    @26
    wa
    #
    @28
    vw
    cv
    #
    cF
    cfv
    #
    @25
    wceq
    #
    vw
    @3
    wrex
    #
    @27
    @1
    @28
    @33
    wi
    @26
    @1
    @28
    @33
    vw
    @25
    @3
    cF
    fvelima
    ex
    adantr
    @29
    @33
    @32
    vw
    @20
    wrex
    #
    @27
    @26
    @33
    @34
    wi
    @1
    @26
    @32
    @32
    vw
    @3
    @20
    @26
    @30
    @3
    wcel
    #
    @32
    wa
    #
    @30
    @20
    wcel
    #
    @32
    @26
    @36
    @35
    @31
    cB
    wcel
    #
    wa
    #
    @37
    @26
    @32
    @38
    @35
    @25
    cB
    @31
    eleq1a
    anim2d
    @19
    @38
    vy
    @30
    @3
    @17
    @30
    wceq
    @18
    @31
    cB
    @17
    @30
    cF
    fveq2
    eleq1d
    elrab
    #
    syl6ibr
    @36
    @32
    wi
    @26
    @35
    @32
    simpr
    a1i
    jcad
    reximdv2
    adantl
    @1
    @27
    @34
    wb
    #
    @26
    @1
    cF
    @2
    wfn
    #
    @41
    cF
    funfn
    @42
    @20
    @2
    wss
    @41
    @20
    @3
    @2
    @24
    cA
    @2
    inss2
    sstri
    vw
    @2
    @20
    @25
    cF
    fvelimab
    mpan2
    sylbi
    adantr
    sylibrd
    syld
    adantlr
    mpd
    ex
    @1
    @27
    @26
    wi
    @5
    @1
    @27
    @34
    @26
    @1
    @27
    @34
    vw
    @25
    @20
    cF
    fvelima
    ex
    @32
    @26
    vw
    @20
    @37
    @39
    @32
    @26
    wi
    #
    @40
    @38
    @43
    @35
    @32
    @38
    @26
    @31
    @25
    cB
    eleq1
    biimpcd
    adantl
    sylbi
    rexlimiv
    syl6
    adantr
    impbid
    eqrdv
    @15
    @21
    @23
    wa
    vx
    @20
    @19
    vy
    @3
    cA
    @2
    ssimaex.1
    inex1
    rabex
    @6
    @20
    wceq
    #
    @14
    @21
    @9
    @23
    @6
    @20
    @3
    sseq1
    @44
    @8
    @22
    cB
    @6
    @20
    cF
    imaeq2
    eqeq2d
    anbi12d
    spcev
    sylancr
    @15
    @10
    vx
    @14
    @7
    @9
    @14
    @3
    cA
    wss
    @7
    cA
    @2
    inss1
    @6
    @3
    cA
    sstr
    mpan2
    anim1i
    eximi
    syl
    sylan2br
end
