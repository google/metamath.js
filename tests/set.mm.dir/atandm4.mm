include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "cc.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "wne.mm"
include "wa.mm"
include "caddc.mm"
include "cc0.mm"
include "atandm3.mm"
include "cmin.mm"
include "wceq.mm"
include "wb.mm"
include "sqcl.mm"
include "neg1cn.mm"
include "subeq0.mm"
include "sylancl.mm"
include "ax-1cn.mm"
include "subneg.mm"
include "addcom.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "bitr3d.mm"
include "necon3bid.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem atandm4
  let cA: class A


  assert |- ( A e. dom arctan <-> ( A e. CC /\ ( 1 + ( A ^ 2 ) ) =/= 0 ) )

  proof
    cA
    catan
    cdm
    wcel
    cA
    cc
    wcel
    #
    cA
    c2
    cexp
    co
    #
    c1
    cneg
    #
    wne
    #
    wa
    @0
    c1
    @1
    caddc
    co
    #
    cc0
    wne
    #
    wa
    cA
    atandm3
    @0
    @3
    @5
    @0
    @1
    @2
    @4
    cc0
    @0
    @1
    @2
    cmin
    co
    #
    cc0
    wceq
    #
    @1
    @2
    wceq
    #
    @4
    cc0
    wceq
    @0
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    @7
    @8
    wb
    cA
    sqcl
    #
    neg1cn
    @1
    @2
    subeq0
    sylancl
    @0
    @6
    @4
    cc0
    @0
    @6
    @1
    c1
    caddc
    co
    #
    @4
    @0
    @9
    c1
    cc
    wcel
    #
    @6
    @11
    wceq
    @10
    ax-1cn
    @1
    c1
    subneg
    sylancl
    @0
    @9
    @12
    @11
    @4
    wceq
    @10
    ax-1cn
    @1
    c1
    addcom
    sylancl
    eqtrd
    eqeq1d
    bitr3d
    necon3bid
    pm5.32i
    bitri
end
