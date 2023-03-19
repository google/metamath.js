include "cep.mm"
include "wfr.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "fr2nr.mm"
include "wb.mm"
include "epelg.mm"
include "bi2anan9r.mm"
include "adantl.mm"
include "mtbid.mm"

theorem efrn2lp
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( _E Fr A /\ ( B e. A /\ C e. A ) ) -> -. ( B e. C /\ C e. B ) )

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
    wa
    #
    wa
    cB
    cC
    cep
    wbr
    #
    cC
    cB
    cep
    wbr
    #
    wa
    #
    cB
    cC
    wcel
    #
    cC
    cB
    wcel
    #
    wa
    #
    cA
    cB
    cC
    cep
    fr2nr
    @3
    @6
    @9
    wb
    @0
    @2
    @4
    @7
    @1
    @5
    @8
    cB
    cC
    cA
    epelg
    cC
    cB
    cA
    epelg
    bi2anan9r
    adantl
    mtbid
end
