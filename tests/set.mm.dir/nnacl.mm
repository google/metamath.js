include "com.mm"
include "wcel.mm"
include "coa.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "c0.mm"
include "csuc.mm"
include "nna0.mm"
include "ibir.mm"
include "wa.mm"
include "peano2.mm"
include "nnasuc.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "finds2.mm"
include "vtoclga.mm"
include "impcom.mm"

theorem nnacl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. _om /\ B e. _om ) -> ( A +o B ) e. _om )

  proof
    cB
    com
    wcel
    cA
    com
    wcel
    #
    cA
    cB
    coa
    co
    #
    com
    wcel
    #
    @0
    cA
    vx
    cv
    #
    coa
    co
    #
    com
    wcel
    #
    wi
    @0
    @2
    wi
    vx
    cB
    com
    @3
    cB
    wceq
    #
    @5
    @2
    @0
    @6
    @4
    @1
    com
    @3
    cB
    cA
    coa
    oveq2
    eleq1d
    imbi2d
    @5
    cA
    c0
    coa
    co
    #
    com
    wcel
    #
    cA
    vy
    cv
    #
    coa
    co
    #
    com
    wcel
    #
    cA
    @9
    csuc
    #
    coa
    co
    #
    com
    wcel
    #
    @0
    vx
    vy
    @3
    c0
    wceq
    @4
    @7
    com
    @3
    c0
    cA
    coa
    oveq2
    eleq1d
    @3
    @9
    wceq
    @4
    @10
    com
    @3
    @9
    cA
    coa
    oveq2
    eleq1d
    @3
    @12
    wceq
    @4
    @13
    com
    @3
    @12
    cA
    coa
    oveq2
    eleq1d
    @0
    @8
    @0
    @7
    cA
    com
    cA
    nna0
    eleq1d
    ibir
    @0
    @9
    com
    wcel
    #
    @11
    @14
    wi
    @11
    @14
    @0
    @15
    wa
    #
    @10
    csuc
    #
    com
    wcel
    @10
    peano2
    @16
    @13
    @17
    com
    cA
    @9
    nnasuc
    eleq1d
    syl5ibr
    expcom
    finds2
    vtoclga
    impcom
end
