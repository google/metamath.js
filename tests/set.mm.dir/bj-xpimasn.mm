include "cxp.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "wcel.mm"
include "wn.mm"
include "xpima.mm"
include "disjsn.mm"
include "eqid.mm"
include "ifbieq2i.mm"
include "ifnot.mm"
include "3eqtri.mm"

theorem bj-xpimasn
  let cA: class A
  let cB: class B
  let cX: class X


  assert |- ( ( A X. B ) " { X } ) = if ( X e. A , B , (/) )

  proof
    cA
    cB
    cxp
    cX
    csn
    #
    cima
    cA
    @0
    cin
    c0
    wceq
    #
    c0
    cB
    cif
    cX
    cA
    wcel
    #
    wn
    #
    c0
    cB
    cif
    @2
    cB
    c0
    cif
    cA
    cB
    @0
    xpima
    @1
    @3
    cB
    cB
    c0
    cA
    cX
    disjsn
    cB
    eqid
    ifbieq2i
    @2
    c0
    cB
    ifnot
    3eqtri
end
