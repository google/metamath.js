include "cxr.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "breq12.mm"
include "id.mm"
include "xnegeq.mm"
include "oveqan12rd.mm"
include "oveqan12d.mm"
include "ifbieq12d.mm"
include "xrsds.mm"
include "ovex.mm"
include "ifex.mm"
include "ovmpt2a.mm"

theorem xrsdsval
  let cA: class A
  let cB: class B
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  assume xrsds.d: |- D = ( dist ` RR*s )


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A D B ) = if ( A <_ B , ( B +e -e A ) , ( A +e -e B ) ) )

  proof
    vx
    vy
    cA
    cB
    cxr
    cxr
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @1
    @0
    cxne
    #
    cxad
    co
    #
    @0
    @1
    cxne
    #
    cxad
    co
    #
    cif
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cxne
    #
    cxad
    co
    #
    cA
    cB
    cxne
    #
    cxad
    co
    #
    cif
    cD
    @0
    cA
    wceq
    #
    @1
    cB
    wceq
    #
    wa
    @2
    @7
    @4
    @6
    @9
    @11
    @0
    cA
    @1
    cB
    cle
    breq12
    @13
    @12
    @1
    cB
    @3
    @8
    cxad
    @13
    id
    @0
    cA
    xnegeq
    oveqan12rd
    @12
    @13
    @0
    cA
    @5
    @10
    cxad
    @12
    id
    @1
    cB
    xnegeq
    oveqan12d
    ifbieq12d
    vx
    vy
    cD
    xrsds.d
    xrsds
    @7
    @9
    @11
    cB
    @8
    cxad
    ovex
    cA
    @10
    cxad
    ovex
    ifex
    ovmpt2a
end
