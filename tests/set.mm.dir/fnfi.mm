include "wfn.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "wceq.mm"
include "fnresdm.mm"
include "adantr.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "reseq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "res0.mm"
include "0fin.mm"
include "eqeltri.mm"
include "a1i.mm"
include "resundi.mm"
include "cfv.mm"
include "cop.mm"
include "wss.mm"
include "snfi.mm"
include "wfun.mm"
include "fnfun.mm"
include "funressn.mm"
include "syl.mm"
include "ssfi.mm"
include "sylancr.mm"
include "unfi.mm"
include "sylan2.mm"
include "syl5eqel.mm"
include "expcom.mm"
include "a2i.mm"
include "findcard2.mm"
include "anabsi7.mm"
include "eqeltrrd.mm"

theorem fnfi
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( ( F Fn A /\ A e. Fin ) -> F e. Fin )

  proof
    cF
    cA
    wfn
    #
    cA
    cfn
    wcel
    #
    wa
    #
    cF
    cA
    cres
    #
    cF
    cfn
    @0
    @3
    cF
    wceq
    @1
    cA
    cF
    fnresdm
    adantr
    @0
    @1
    @3
    cfn
    wcel
    #
    @2
    cF
    vx
    cv
    #
    cres
    #
    cfn
    wcel
    #
    wi
    @2
    cF
    c0
    cres
    #
    cfn
    wcel
    #
    wi
    @2
    cF
    vy
    cv
    #
    cres
    #
    cfn
    wcel
    #
    wi
    #
    @2
    cF
    @10
    vz
    cv
    #
    csn
    #
    cun
    #
    cres
    #
    cfn
    wcel
    #
    wi
    #
    @2
    @4
    wi
    vx
    vy
    vz
    cA
    @5
    c0
    wceq
    #
    @7
    @9
    @2
    @20
    @6
    @8
    cfn
    @5
    c0
    cF
    reseq2
    eleq1d
    imbi2d
    @5
    @10
    wceq
    #
    @7
    @12
    @2
    @21
    @6
    @11
    cfn
    @5
    @10
    cF
    reseq2
    eleq1d
    imbi2d
    @5
    @16
    wceq
    #
    @7
    @18
    @2
    @22
    @6
    @17
    cfn
    @5
    @16
    cF
    reseq2
    eleq1d
    imbi2d
    @5
    cA
    wceq
    #
    @7
    @4
    @2
    @23
    @6
    @3
    cfn
    @5
    cA
    cF
    reseq2
    eleq1d
    imbi2d
    @9
    @2
    @8
    c0
    cfn
    cF
    res0
    0fin
    eqeltri
    a1i
    @13
    @19
    wi
    @10
    cfn
    wcel
    @2
    @12
    @18
    @12
    @2
    @18
    @12
    @2
    wa
    @17
    @11
    cF
    @15
    cres
    #
    cun
    #
    cfn
    cF
    @10
    @15
    resundi
    @2
    @12
    @24
    cfn
    wcel
    #
    @25
    cfn
    wcel
    @2
    @14
    @14
    cF
    cfv
    cop
    #
    csn
    #
    cfn
    wcel
    @24
    @28
    wss
    #
    @26
    @27
    snfi
    @0
    @29
    @1
    @0
    cF
    wfun
    @29
    cA
    cF
    fnfun
    @14
    cF
    funressn
    syl
    adantr
    @28
    @24
    ssfi
    sylancr
    @11
    @24
    unfi
    sylan2
    syl5eqel
    expcom
    a2i
    a1i
    findcard2
    anabsi7
    eqeltrrd
end
