include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wb.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "oveq1d.mm"
include "bibi12d.mm"
include "breq2d.mm"
include "oveq1.mm"
include "syl.mm"
include "0cn.mm"
include "elimel.mm"
include "abs2sqlti.mm"
include "dedth2h.mm"

theorem abs2sqlt
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( abs ` A ) < ( abs ` B ) <-> ( ( abs ` A ) ^ 2 ) < ( ( abs ` B ) ^ 2 ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cA
    cabs
    cfv
    #
    cB
    cabs
    cfv
    #
    clt
    wbr
    #
    @2
    c2
    cexp
    co
    #
    @3
    c2
    cexp
    co
    #
    clt
    wbr
    #
    wb
    @0
    cA
    cc0
    cif
    #
    cabs
    cfv
    #
    @3
    clt
    wbr
    #
    @9
    c2
    cexp
    co
    #
    @6
    clt
    wbr
    #
    wb
    @9
    @1
    cB
    cc0
    cif
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    @11
    @14
    c2
    cexp
    co
    #
    clt
    wbr
    #
    wb
    cA
    cB
    cc0
    cc0
    cA
    @8
    wceq
    #
    @4
    @10
    @7
    @12
    @18
    @2
    @9
    @3
    clt
    cA
    @8
    cabs
    fveq2
    #
    breq1d
    @18
    @5
    @11
    @6
    clt
    @18
    @2
    @9
    c2
    cexp
    @19
    oveq1d
    breq1d
    bibi12d
    cB
    @13
    wceq
    #
    @10
    @15
    @12
    @17
    @20
    @3
    @14
    @9
    clt
    cB
    @13
    cabs
    fveq2
    #
    breq2d
    @20
    @3
    @14
    wceq
    #
    @12
    @17
    wb
    @21
    @22
    @6
    @16
    @11
    clt
    @3
    @14
    c2
    cexp
    oveq1
    breq2d
    syl
    bibi12d
    @8
    @13
    cA
    cc0
    cc
    0cn
    elimel
    cB
    cc0
    cc
    0cn
    elimel
    abs2sqlti
    dedth2h
end
