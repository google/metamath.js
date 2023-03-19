include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "psmetf.mm"
include "3ad2ant1.mm"
include "psmet0.mm"
include "3adant3.mm"
include "jca.mm"
include "psmetge0.mm"
include "psmetsym.mm"
include "jca32.mm"

theorem distspace
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let cX: class X
  assume distspace.x: |- X = ( Base ` G )
  assume distspace.d: |- D = ( dist ` G )


  assert |- ( ( D e. ( PsMet ` X ) /\ A e. X /\ B e. X ) -> ( ( D : ( X X. X ) --> RR* /\ ( A D A ) = 0 ) /\ ( 0 <_ ( A D B ) /\ ( A D B ) = ( B D A ) ) ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cX
    cX
    cxp
    cxr
    cD
    wf
    #
    cA
    cA
    cD
    co
    cc0
    wceq
    #
    wa
    cc0
    cA
    cB
    cD
    co
    #
    cle
    wbr
    @6
    cB
    cA
    cD
    co
    wceq
    @3
    @4
    @5
    @0
    @1
    @4
    @2
    cD
    cX
    psmetf
    3ad2ant1
    @0
    @1
    @5
    @2
    cA
    cD
    cX
    psmet0
    3adant3
    jca
    cA
    cB
    cD
    cX
    psmetge0
    cA
    cB
    cD
    cX
    psmetsym
    jca32
end
