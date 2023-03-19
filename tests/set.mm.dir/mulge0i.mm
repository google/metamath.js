include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "mulge0.mm"
include "an4s.mm"
include "mpanl12.mm"

theorem mulge0i
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( ( 0 <_ A /\ 0 <_ B ) -> 0 <_ ( A x. B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    cc0
    cA
    cB
    cmul
    co
    cle
    wbr
    #
    lt2.1
    lt2.2
    @0
    @2
    @1
    @3
    @4
    cA
    cB
    mulge0
    an4s
    mpanl12
end
