include "wcel.mm"
include "cvv.mm"
include "cmpt.mm"
include "cixp.mm"
include "wral.mm"
include "wb.mm"
include "elex.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "csb.mm"
include "wa.mm"
include "w3a.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvixp.mm"
include "eleq2i.mm"
include "elixp2.mm"
include "3anass.mm"
include "3bitri.mm"
include "eqid.mm"
include "fnmpt.mm"
include "fvmpt2.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "ralimiaa.mm"
include "jca.mm"
include "wf.mm"
include "wi.mm"
include "dffn2.mm"
include "fmpt.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "ralim.mm"
include "syl.mm"
include "sylbir.mm"
include "sylbi.mm"
include "imp.mm"
include "impbii.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfel.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "cbvral.mm"
include "anbi2i.mm"
include "bitri.mm"
include "mptexg.mm"
include "biantrurd.mm"
include "syl5rbb.mm"
include "syl5bb.mm"

theorem mptelixpg
  let vx: setvar x
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let vy: setvar y

  disjoint I x
  disjoint I y
  disjoint x y
  disjoint J y
  disjoint K y
  assert |- ( I e. V -> ( ( x e. I |-> J ) e. X_ x e. I K <-> A. x e. I J e. K ) )

  proof
    cI
    cV
    wcel
    cI
    cvv
    wcel
    #
    vx
    cI
    cJ
    cmpt
    #
    vx
    cI
    cK
    cixp
    #
    wcel
    #
    cJ
    cK
    wcel
    #
    vx
    cI
    wral
    #
    wb
    cI
    cV
    elex
    @3
    @1
    cvv
    wcel
    #
    @1
    cI
    wfn
    #
    vy
    cv
    #
    @1
    cfv
    #
    vx
    @8
    cK
    csb
    #
    wcel
    #
    vy
    cI
    wral
    #
    wa
    #
    wa
    #
    @0
    @5
    @3
    @1
    vy
    cI
    @10
    cixp
    #
    wcel
    @6
    @7
    @12
    w3a
    @14
    @2
    @15
    @1
    vx
    vy
    cI
    cK
    @10
    vy
    cK
    nfcv
    vx
    @8
    cK
    nfcsb1v
    #
    vx
    @8
    cK
    csbeq1a
    #
    cbvixp
    eleq2i
    vy
    cI
    @10
    @1
    elixp2
    @6
    @7
    @12
    3anass
    3bitri
    @5
    @13
    @0
    @14
    @5
    @7
    vx
    cv
    #
    @1
    cfv
    #
    cK
    wcel
    #
    vx
    cI
    wral
    #
    wa
    #
    @13
    @5
    @22
    @5
    @7
    @21
    vx
    cI
    cJ
    @1
    cK
    @1
    eqid
    #
    fnmpt
    @4
    @20
    vx
    cI
    @18
    cI
    wcel
    #
    @4
    wa
    @19
    cJ
    cK
    vx
    cI
    cJ
    cK
    @1
    @23
    fvmpt2
    @24
    @4
    simpr
    eqeltrd
    ralimiaa
    jca
    @7
    @21
    @5
    @7
    cI
    cvv
    @1
    wf
    #
    @21
    @5
    wi
    #
    cI
    @1
    dffn2
    @25
    cJ
    cvv
    wcel
    #
    vx
    cI
    wral
    #
    @26
    vx
    cI
    cvv
    cJ
    @1
    @23
    fmpt
    @28
    @20
    @4
    wi
    #
    vx
    cI
    wral
    @26
    @27
    @29
    vx
    cI
    @24
    @27
    wa
    #
    @20
    @4
    @30
    @19
    cJ
    cK
    vx
    cI
    cJ
    cvv
    @1
    @23
    fvmpt2
    eleq1d
    biimpd
    ralimiaa
    @20
    @4
    vx
    cI
    ralim
    syl
    sylbir
    sylbi
    imp
    impbii
    @21
    @12
    @7
    @20
    @11
    vx
    vy
    cI
    @20
    vy
    nfv
    vx
    @9
    @10
    vx
    cI
    cJ
    @8
    nffvmpt1
    @16
    nfel
    vx
    vy
    weq
    @19
    @9
    cK
    @10
    @18
    @8
    @1
    fveq2
    @17
    eleq12d
    cbvral
    anbi2i
    bitri
    @0
    @6
    @13
    vx
    cI
    cJ
    cvv
    mptexg
    biantrurd
    syl5rbb
    syl5bb
    syl
end
