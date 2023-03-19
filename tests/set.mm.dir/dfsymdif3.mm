include "cin.mm"
include "cdif.mm"
include "cun.mm"
include "csymdif.mm"
include "difin.mm"
include "incom.mm"
include "difeq2i.mm"
include "eqtri.mm"
include "uneq12i.mm"
include "difundir.mm"
include "df-symdif.mm"
include "3eqtr4ri.mm"

theorem dfsymdif3
  let cA: class A
  let cB: class B


  assert |- ( A /_\ B ) = ( ( A u. B ) \ ( A i^i B ) )

  proof
    cA
    cA
    cB
    cin
    #
    cdif
    #
    cB
    @0
    cdif
    #
    cun
    cA
    cB
    cdif
    #
    cB
    cA
    cdif
    #
    cun
    cA
    cB
    cun
    @0
    cdif
    cA
    cB
    csymdif
    @1
    @3
    @2
    @4
    cA
    cB
    difin
    @2
    cB
    cB
    cA
    cin
    #
    cdif
    @4
    @0
    @5
    cB
    cA
    cB
    incom
    difeq2i
    cB
    cA
    difin
    eqtri
    uneq12i
    cA
    cB
    @0
    difundir
    cA
    cB
    df-symdif
    3eqtr4ri
end
