include "chil.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "cfv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "c0v.mm"
include "wne.mm"
include "csp.mm"
include "cr.mm"
include "wb.mm"
include "wi.mm"
include "cif.mm"
include "cc0.mm"
include "fveq2.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "id.mm"
include "oveq12d.mm"
include "bibi1d.mm"
include "imbi12d.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "eleq1.mm"
include "bibi2d.mm"
include "ifhvhv0.mm"
include "0cn.mm"
include "elimel.mm"
include "eigrei.mm"
include "dedth2h.mm"
include "imp.mm"

theorem eigre
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( ( A e. ~H /\ B e. CC ) /\ ( ( T ` A ) = ( B .h A ) /\ A =/= 0h ) ) -> ( ( A .ih ( T ` A ) ) = ( ( T ` A ) .ih A ) <-> B e. RR ) )

  proof
    cA
    chil
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    cA
    cT
    cfv
    #
    cB
    cA
    csm
    co
    #
    wceq
    #
    cA
    c0v
    wne
    #
    wa
    #
    cA
    @2
    csp
    co
    #
    @2
    cA
    csp
    co
    #
    wceq
    #
    cB
    cr
    wcel
    #
    wb
    #
    @0
    @1
    @6
    @11
    wi
    @0
    cA
    c0v
    cif
    #
    cT
    cfv
    #
    cB
    @12
    csm
    co
    #
    wceq
    #
    @12
    c0v
    wne
    #
    wa
    #
    @12
    @13
    csp
    co
    #
    @13
    @12
    csp
    co
    #
    wceq
    #
    @10
    wb
    #
    wi
    @13
    @1
    cB
    cc0
    cif
    #
    @12
    csm
    co
    #
    wceq
    #
    @16
    wa
    #
    @20
    @22
    cr
    wcel
    #
    wb
    #
    wi
    cA
    cB
    c0v
    cc0
    cA
    @12
    wceq
    #
    @6
    @17
    @11
    @21
    @28
    @4
    @15
    @5
    @16
    @28
    @2
    @13
    @3
    @14
    cA
    @12
    cT
    fveq2
    #
    cA
    @12
    cB
    csm
    oveq2
    eqeq12d
    cA
    @12
    c0v
    neeq1
    anbi12d
    @28
    @9
    @20
    @10
    @28
    @7
    @18
    @8
    @19
    @28
    cA
    @12
    @2
    @13
    csp
    @28
    id
    #
    @29
    oveq12d
    @28
    @2
    @13
    cA
    @12
    csp
    @29
    @30
    oveq12d
    eqeq12d
    bibi1d
    imbi12d
    cB
    @22
    wceq
    #
    @17
    @25
    @21
    @27
    @31
    @15
    @24
    @16
    @31
    @14
    @23
    @13
    cB
    @22
    @12
    csm
    oveq1
    eqeq2d
    anbi1d
    @31
    @10
    @26
    @20
    cB
    @22
    cr
    eleq1
    bibi2d
    imbi12d
    @12
    @22
    cT
    cA
    ifhvhv0
    cB
    cc0
    cc
    0cn
    elimel
    eigrei
    dedth2h
    imp
end
