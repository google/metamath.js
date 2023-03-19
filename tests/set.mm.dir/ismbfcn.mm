include "cc.mm"
include "wf.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cmbf.mm"
include "cre.mm"
include "ccom.mm"
include "cim.mm"
include "wa.mm"
include "mbfdm.mm"
include "fdm.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "adantr.mm"
include "cr.mm"
include "wceq.mm"
include "ref.mm"
include "fco.mm"
include "mpan.mm"
include "syl.mm"
include "wb.mm"
include "cpm.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "ismbf.mm"
include "imf.mm"
include "anbi12d.mm"
include "r19.26.mm"
include "syl6bbr.mm"
include "wss.mm"
include "mblss.mm"
include "cvv.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "sylan2.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "ismbf1.mm"
include "syl6rbbr.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem ismbfcn
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C


  assert |- ( F : A --> CC -> ( F e. MblFn <-> ( ( Re o. F ) e. MblFn /\ ( Im o. F ) e. MblFn ) ) )

  proof
    cA
    cc
    cF
    wf
    #
    cA
    cvol
    cdm
    #
    wcel
    #
    cF
    cmbf
    wcel
    #
    cre
    cF
    ccom
    #
    cmbf
    wcel
    #
    cim
    cF
    ccom
    #
    cmbf
    wcel
    #
    wa
    #
    @3
    cF
    cdm
    #
    @1
    wcel
    @0
    @2
    cF
    mbfdm
    @0
    @9
    cA
    @1
    cA
    cc
    cF
    fdm
    eleq1d
    syl5ib
    @8
    @4
    cdm
    #
    @1
    wcel
    #
    @0
    @2
    @5
    @11
    @7
    @4
    mbfdm
    adantr
    @0
    @10
    cA
    @1
    @0
    cA
    cr
    @4
    wf
    #
    @10
    cA
    wceq
    cc
    cr
    cre
    wf
    @0
    @12
    ref
    cA
    cc
    cr
    cre
    cF
    fco
    mpan
    #
    cA
    cr
    @4
    fdm
    syl
    eleq1d
    syl5ib
    @0
    @2
    @3
    @8
    wb
    @0
    @2
    wa
    #
    @8
    cF
    cc
    cr
    cpm
    co
    wcel
    #
    @4
    ccnv
    vx
    cv
    #
    cima
    @1
    wcel
    #
    @6
    ccnv
    @16
    cima
    @1
    wcel
    #
    wa
    vx
    cioo
    crn
    #
    wral
    #
    wa
    #
    @3
    @14
    @8
    @20
    @21
    @14
    @8
    @17
    vx
    @19
    wral
    #
    @18
    vx
    @19
    wral
    #
    wa
    @20
    @14
    @5
    @22
    @7
    @23
    @14
    @12
    @5
    @22
    wb
    @0
    @12
    @2
    @13
    adantr
    vx
    cA
    @4
    ismbf
    syl
    @14
    cA
    cr
    @6
    wf
    #
    @7
    @23
    wb
    @0
    @24
    @2
    cc
    cr
    cim
    wf
    @0
    @24
    imf
    cA
    cc
    cr
    cim
    cF
    fco
    mpan
    adantr
    vx
    cA
    @6
    ismbf
    syl
    anbi12d
    @17
    @18
    vx
    @19
    r19.26
    syl6bbr
    @14
    @15
    @20
    @2
    @0
    cA
    cr
    wss
    #
    @15
    cA
    mblss
    cc
    cvv
    wcel
    cr
    cvv
    wcel
    @0
    @25
    wa
    @15
    cnex
    reex
    cc
    cr
    cA
    cF
    cvv
    cvv
    elpm2r
    mpanl12
    sylan2
    biantrurd
    bitrd
    vx
    cF
    ismbf1
    syl6rbbr
    ex
    pm5.21ndd
end
