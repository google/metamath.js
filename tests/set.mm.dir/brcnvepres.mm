include "wcel.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "wbr.mm"
include "wa.mm"
include "brresALTV.mm"
include "brcnvep.mm"
include "anbi2d.mm"
include "sylan9bbr.mm"

theorem brcnvepres
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W


  assert |- ( ( B e. V /\ C e. W ) -> ( B ( `' _E |` A ) C <-> ( B e. A /\ C e. B ) ) )

  proof
    cC
    cW
    wcel
    cB
    cC
    cep
    ccnv
    #
    cA
    cres
    wbr
    cB
    cA
    wcel
    #
    cB
    cC
    @0
    wbr
    #
    wa
    cB
    cV
    wcel
    #
    @1
    cC
    cB
    wcel
    #
    wa
    cA
    cB
    cC
    @0
    cW
    brresALTV
    @3
    @2
    @4
    @1
    cB
    cC
    cV
    brcnvep
    anbi2d
    sylan9bbr
end
