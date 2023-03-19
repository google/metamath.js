include "cep.mm"
include "wfr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "fr3nr.mm"
include "wb.mm"
include "epelg.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "3ad2ant1.mm"
include "3anbi123d.mm"
include "adantl.mm"
include "mtbid.mm"

theorem epne3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( _E Fr A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> -. ( B e. C /\ C e. D /\ D e. B ) )

  proof
    cA
    cep
    wfr
    #
    cB
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    cD
    cA
    wcel
    #
    w3a
    #
    wa
    cB
    cC
    cep
    wbr
    #
    cC
    cD
    cep
    wbr
    #
    cD
    cB
    cep
    wbr
    #
    w3a
    #
    cB
    cC
    wcel
    #
    cC
    cD
    wcel
    #
    cD
    cB
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    cD
    cep
    fr3nr
    @4
    @8
    @12
    wb
    @0
    @4
    @5
    @9
    @6
    @10
    @7
    @11
    @2
    @1
    @5
    @9
    wb
    @3
    cB
    cC
    cA
    epelg
    3ad2ant2
    @3
    @1
    @6
    @10
    wb
    @2
    cC
    cD
    cA
    epelg
    3ad2ant3
    @1
    @2
    @7
    @11
    wb
    @3
    cD
    cB
    cA
    epelg
    3ad2ant1
    3anbi123d
    adantl
    mtbid
end
