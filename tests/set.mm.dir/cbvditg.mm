include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "citg.mm"
include "cneg.mm"
include "cif.mm"
include "cdit.mm"
include "biid.mm"
include "cbvitg.mm"
include "negeqi.mm"
include "ifbieq12i.mm"
include "df-ditg.mm"
include "3eqtr4i.mm"

theorem cbvditg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume cbvditg.1: |- ( x = y -> C = D )
  assume cbvditg.2: |- F/_ y C
  assume cbvditg.3: |- F/_ x D

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- S_ [ A -> B ] C _d x = S_ [ A -> B ] D _d y

  proof
    cA
    cB
    cle
    wbr
    #
    vx
    cA
    cB
    cioo
    co
    #
    cC
    citg
    #
    vx
    cB
    cA
    cioo
    co
    #
    cC
    citg
    #
    cneg
    #
    cif
    @0
    vy
    @1
    cD
    citg
    #
    vy
    @3
    cD
    citg
    #
    cneg
    #
    cif
    vx
    cA
    cB
    cC
    cdit
    vy
    cA
    cB
    cD
    cdit
    @0
    @0
    @2
    @5
    @6
    @8
    @0
    biid
    vx
    vy
    @1
    cC
    cD
    cbvditg.1
    cbvditg.2
    cbvditg.3
    cbvitg
    @4
    @7
    vx
    vy
    @3
    cC
    cD
    cbvditg.1
    cbvditg.2
    cbvditg.3
    cbvitg
    negeqi
    ifbieq12i
    vx
    cA
    cB
    cC
    df-ditg
    vy
    cA
    cB
    cD
    df-ditg
    3eqtr4i
end
