include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "cpr.mm"
include "cpw.mm"
include "crab.mm"
include "csn.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wss.mm"
include "elpwi.mm"
include "cfn.mm"
include "prfi.mm"
include "ssfi.mm"
include "mpan.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "hash2.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqeq2d.mm"
include "wb.mm"
include "com.mm"
include "2onn.mm"
include "nnfi.mm"
include "ax-mp.mm"
include "hashen.mm"
include "mpan2.mm"
include "bitrd.mm"
include "hash2pwpr.mm"
include "a1d.mm"
include "ex.mm"
include "syl6bir.mm"
include "com23.mm"
include "syl.mm"
include "mpcom.mm"
include "imp.mm"
include "com12.mm"
include "c0.mm"
include "cun.mm"
include "wo.mm"
include "prex.mm"
include "prid2.mm"
include "olcd.mm"
include "elun.mm"
include "sylibr.mm"
include "pwpr.mm"
include "syl6eleqr.mm"
include "adantr.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "pr2nelem.mm"
include "breq1.mm"
include "jca.mm"
include "impbid.mm"
include "elrab.mm"
include "velsn.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem pr2pwpr
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vs: setvar s

  disjoint A p
  disjoint B p
  disjoint A s
  disjoint p s
  disjoint B s
  disjoint V s
  disjoint W s
  assert |- ( ( A e. V /\ B e. W /\ A =/= B ) -> { p e. ~P { A , B } | p ~~ 2o } = { { A , B } } )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    cA
    cB
    wne
    w3a
    #
    vs
    vp
    cv
    #
    c2o
    cen
    wbr
    #
    vp
    cA
    cB
    cpr
    #
    cpw
    #
    crab
    #
    @3
    csn
    #
    @0
    vs
    cv
    #
    @4
    wcel
    #
    @7
    c2o
    cen
    wbr
    #
    wa
    #
    @7
    @3
    wceq
    #
    @7
    @5
    wcel
    @7
    @6
    wcel
    @0
    @10
    @11
    @10
    @0
    @11
    @8
    @9
    @0
    @11
    wi
    #
    @7
    @3
    wss
    #
    @8
    @9
    @12
    wi
    #
    @7
    @3
    elpwi
    @13
    @7
    cfn
    wcel
    #
    @8
    @14
    wi
    @3
    cfn
    wcel
    @13
    @15
    cA
    cB
    prfi
    @3
    @7
    ssfi
    mpan
    @15
    @9
    @8
    @12
    @15
    @9
    @7
    chash
    cfv
    #
    c2
    wceq
    #
    @8
    @12
    wi
    @15
    @17
    @16
    c2o
    chash
    cfv
    #
    wceq
    #
    @9
    @15
    c2
    @18
    @16
    c2
    @18
    wceq
    @15
    @18
    c2
    hash2
    eqcomi
    a1i
    eqeq2d
    @15
    c2o
    cfn
    wcel
    #
    @19
    @9
    wb
    c2o
    com
    wcel
    @20
    2onn
    c2o
    nnfi
    ax-mp
    @7
    c2o
    hashen
    mpan2
    bitrd
    @17
    @8
    @12
    @17
    @8
    wa
    @11
    @0
    @7
    cA
    cB
    hash2pwpr
    a1d
    ex
    syl6bir
    com23
    syl
    mpcom
    imp
    com12
    @0
    @11
    @10
    @0
    @11
    wa
    #
    @8
    @9
    @21
    @8
    @3
    @4
    wcel
    #
    @0
    @22
    @11
    @0
    @3
    c0
    cA
    csn
    cpr
    #
    cB
    csn
    #
    @3
    cpr
    #
    cun
    #
    @4
    @0
    @3
    @23
    wcel
    #
    @3
    @25
    wcel
    #
    wo
    @3
    @26
    wcel
    @0
    @28
    @27
    @28
    @0
    @24
    @3
    cA
    cB
    prex
    prid2
    a1i
    olcd
    @3
    @23
    @25
    elun
    sylibr
    cA
    cB
    pwpr
    syl6eleqr
    adantr
    @11
    @8
    @22
    wb
    @0
    @7
    @3
    @4
    eleq1
    adantl
    mpbird
    @21
    @9
    @3
    c2o
    cen
    wbr
    #
    @0
    @29
    @11
    cA
    cB
    cV
    cW
    pr2nelem
    adantr
    @11
    @9
    @29
    wb
    @0
    @7
    @3
    c2o
    cen
    breq1
    adantl
    mpbird
    jca
    ex
    impbid
    @2
    @9
    vp
    @7
    @4
    @1
    @7
    c2o
    cen
    breq1
    elrab
    vs
    @3
    velsn
    3bitr4g
    eqrdv
end
