include "cdit.mm"
include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "citg.mm"
include "cneg.mm"
include "cif.mm"
include "cc0.mm"
include "df-ditg.mm"
include "wceq.mm"
include "c0.mm"
include "iooid.mm"
include "itgeq1.mm"
include "ax-mp.mm"
include "itg0.mm"
include "eqtri.mm"
include "negeqi.mm"
include "neg0.mm"
include "ifeq12.mm"
include "mp2an.mm"
include "ifid.mm"

theorem ditg0
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- S_ [ A -> A ] B _d x = 0

  proof
    vx
    cA
    cA
    cB
    cdit
    cA
    cA
    cle
    wbr
    #
    vx
    cA
    cA
    cioo
    co
    #
    cB
    citg
    #
    @2
    cneg
    #
    cif
    #
    cc0
    vx
    cA
    cA
    cB
    df-ditg
    @4
    @0
    cc0
    cc0
    cif
    #
    cc0
    @2
    cc0
    wceq
    @3
    cc0
    wceq
    @4
    @5
    wceq
    @2
    vx
    c0
    cB
    citg
    #
    cc0
    @1
    c0
    wceq
    @2
    @6
    wceq
    cA
    iooid
    vx
    @1
    c0
    cB
    itgeq1
    ax-mp
    vx
    cB
    itg0
    eqtri
    #
    @3
    cc0
    cneg
    cc0
    @2
    cc0
    @7
    negeqi
    neg0
    eqtri
    @0
    @2
    cc0
    @3
    cc0
    ifeq12
    mp2an
    @0
    cc0
    ifid
    eqtri
    eqtri
end
