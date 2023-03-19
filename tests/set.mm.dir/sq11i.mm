include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "recni.mm"
include "sqvali.mm"
include "eqeq12i.mm"
include "msq11i.mm"
include "syl5bb.mm"

theorem sq11i
  let cA: class A
  let cB: class B
  assume resqcl.1: |- A e. RR
  assume lt2sq.2: |- B e. RR


  assert |- ( ( 0 <_ A /\ 0 <_ B ) -> ( ( A ^ 2 ) = ( B ^ 2 ) <-> A = B ) )

  proof
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    wceq
    cA
    cA
    cmul
    co
    #
    cB
    cB
    cmul
    co
    #
    wceq
    cc0
    cA
    cle
    wbr
    cc0
    cB
    cle
    wbr
    wa
    cA
    cB
    wceq
    @0
    @2
    @1
    @3
    cA
    cA
    resqcl.1
    recni
    sqvali
    cB
    cB
    lt2sq.2
    recni
    sqvali
    eqeq12i
    cA
    cB
    resqcl.1
    lt2sq.2
    msq11i
    syl5bb
end
