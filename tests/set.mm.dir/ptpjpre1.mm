include "wcel.mm"
include "ctop.mm"
include "wf.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "wceq.mm"
include "cuni.mm"
include "cif.mm"
include "cixp.mm"
include "wfn.mm"
include "wral.mm"
include "wb.mm"
include "simplrl.mm"
include "vex.mm"
include "elixp.mm"
include "simprbi.mm"
include "eleq2s.mm"
include "adantl.mm"
include "fveq2.mm"
include "unieqd.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "fveq1.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eleq1d.mm"
include "pm5.32i.mm"
include "eleq2i.mm"
include "bitri.mm"
include "anbi1i.mm"
include "anass.mm"
include "simprl.mm"
include "iftrue.mm"
include "syl5ibrcom.mm"
include "wn.mm"
include "simprr.mm"
include "iffalse.mm"
include "eleq2d.mm"
include "pm2.61d.mm"
include "expr.mm"
include "ralimdv.mm"
include "expimpd.mm"
include "ancomsd.mm"
include "wss.mm"
include "elssuni.mm"
include "ad2antll.mm"
include "sseq12d.mm"
include "ssid.mm"
include "syl6eqss.mm"
include "pm2.61d1.mm"
include "sseld.mm"
include "wi.mm"
include "ad2antrl.mm"
include "jcad.mm"
include "impbid.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem ptpjpre1
  let vw: setvar w
  let cA: class A
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cV: class V
  let cX: class X
  let vz: setvar z
  assume ptpjpre1.1: |- X = X_ k e. A U. ( F ` k )

  disjoint k w
  disjoint A k
  disjoint A w
  disjoint F k
  disjoint F w
  disjoint I k
  disjoint I w
  disjoint U k
  disjoint U w
  disjoint V k
  disjoint V w
  disjoint X w
  disjoint k z
  disjoint w z
  disjoint A z
  disjoint F z
  disjoint I z
  disjoint U z
  disjoint V z
  disjoint X z
  assert |- ( ( ( A e. V /\ F : A --> Top ) /\ ( I e. A /\ U e. ( F ` I ) ) ) -> ( `' ( w e. X |-> ( w ` I ) ) " U ) = X_ k e. A if ( k = I , U , U. ( F ` k ) ) )

  proof
    cA
    cV
    wcel
    cA
    ctop
    cF
    wf
    wa
    #
    cI
    cA
    wcel
    #
    cU
    cI
    cF
    cfv
    #
    wcel
    #
    wa
    wa
    #
    vz
    vw
    cX
    cI
    vw
    cv
    #
    cfv
    #
    cmpt
    #
    ccnv
    cU
    cima
    #
    vk
    cA
    vk
    cv
    #
    cI
    wceq
    #
    cU
    @9
    cF
    cfv
    #
    cuni
    #
    cif
    #
    cixp
    #
    @4
    vz
    cv
    #
    @8
    wcel
    #
    @15
    cA
    wfn
    #
    @9
    @15
    cfv
    #
    @13
    wcel
    #
    vk
    cA
    wral
    #
    wa
    #
    @15
    @14
    wcel
    @4
    @16
    @15
    cX
    wcel
    #
    @15
    @7
    cfv
    #
    cU
    wcel
    #
    wa
    #
    @21
    @4
    cX
    @2
    cuni
    #
    @7
    wf
    @7
    cX
    wfn
    @16
    @25
    wb
    @4
    vw
    cX
    @6
    @26
    @7
    @4
    @5
    cX
    wcel
    #
    wa
    @1
    @9
    @5
    cfv
    #
    @12
    wcel
    #
    vk
    cA
    wral
    #
    @6
    @26
    wcel
    #
    @0
    @1
    @3
    @27
    simplrl
    @27
    @30
    @4
    @30
    @5
    vk
    cA
    @12
    cixp
    #
    cX
    @5
    @32
    wcel
    @5
    cA
    wfn
    @30
    vk
    cA
    @12
    @5
    vw
    vex
    elixp
    simprbi
    ptpjpre1.1
    eleq2s
    adantl
    @29
    @31
    vk
    cI
    cA
    @10
    @28
    @6
    @12
    @26
    @9
    cI
    @5
    fveq2
    @10
    @11
    @2
    @9
    cI
    cF
    fveq2
    unieqd
    #
    eleq12d
    rspcv
    sylc
    @7
    eqid
    #
    fmptd
    cX
    @26
    @7
    ffn
    cX
    @15
    cU
    @7
    elpreima
    3syl
    @25
    @17
    @18
    @12
    wcel
    #
    vk
    cA
    wral
    #
    cI
    @15
    cfv
    #
    cU
    wcel
    #
    wa
    #
    wa
    #
    @4
    @21
    @25
    @22
    @38
    wa
    #
    @40
    @22
    @24
    @38
    @22
    @23
    @37
    cU
    vw
    @15
    @6
    @37
    cX
    @7
    cI
    @5
    @15
    fveq1
    @34
    cI
    @15
    fvex
    fvmpt
    eleq1d
    pm5.32i
    @41
    @17
    @36
    wa
    #
    @38
    wa
    @40
    @22
    @42
    @38
    @22
    @15
    @32
    wcel
    @42
    cX
    @32
    @15
    ptpjpre1.1
    eleq2i
    vk
    cA
    @12
    @15
    vz
    vex
    #
    elixp
    bitri
    anbi1i
    @17
    @36
    @38
    anass
    bitri
    bitri
    @4
    @39
    @20
    @17
    @4
    @39
    @20
    @4
    @38
    @36
    @20
    @4
    @38
    @36
    @20
    @4
    @38
    wa
    @35
    @19
    vk
    cA
    @4
    @38
    @35
    @19
    @4
    @38
    @35
    wa
    wa
    #
    @10
    @19
    @44
    @19
    @10
    @38
    @4
    @38
    @35
    simprl
    @10
    @18
    @37
    @13
    cU
    @9
    cI
    @15
    fveq2
    @10
    cU
    @12
    iftrue
    #
    eleq12d
    #
    syl5ibrcom
    @44
    @19
    @10
    wn
    #
    @35
    @4
    @38
    @35
    simprr
    @47
    @13
    @12
    @18
    @10
    cU
    @12
    iffalse
    #
    eleq2d
    syl5ibrcom
    pm2.61d
    expr
    ralimdv
    expimpd
    ancomsd
    @4
    @20
    @36
    @38
    @4
    @19
    @35
    vk
    cA
    @4
    @13
    @12
    @18
    @4
    @10
    @13
    @12
    wss
    #
    @4
    @49
    @10
    cU
    @26
    wss
    #
    @3
    @50
    @0
    @1
    cU
    @2
    elssuni
    ad2antll
    @10
    @13
    cU
    @12
    @26
    @45
    @33
    sseq12d
    syl5ibrcom
    @47
    @13
    @12
    @12
    @48
    @12
    ssid
    syl6eqss
    pm2.61d1
    sseld
    ralimdv
    @1
    @20
    @38
    wi
    @0
    @3
    @19
    @38
    vk
    cI
    cA
    @46
    rspcv
    ad2antrl
    jcad
    impbid
    anbi2d
    syl5bb
    bitrd
    vk
    cA
    @13
    @15
    @43
    elixp
    syl6bbr
    eqrdv
end
