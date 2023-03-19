include "wnel.mm"
include "cxp.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "c0.mm"
include "cif.mm"
include "bj-xpimasn.mm"
include "wn.mm"
include "wceq.mm"
include "df-nel.mm"
include "iffalse.mm"
include "sylbi.mm"
include "syl5eq.mm"

theorem bj-xpima1sn
  let cA: class A
  let cB: class B
  let cX: class X


  assert |- ( X e/ A -> ( ( A X. B ) " { X } ) = (/) )

  proof
    cX
    cA
    wnel
    #
    cA
    cB
    cxp
    cX
    csn
    cima
    cX
    cA
    wcel
    #
    cB
    c0
    cif
    #
    c0
    cA
    cB
    cX
    bj-xpimasn
    @0
    @1
    wn
    @2
    c0
    wceq
    cX
    cA
    df-nel
    @1
    cB
    c0
    iffalse
    sylbi
    syl5eq
end
