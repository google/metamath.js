include "cdif.mm"
include "cun.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "csymdif.mm"
include "wb.mm"
include "elun.mm"
include "eldif.mm"
include "orbi12i.mm"
include "bitri.mm"
include "df-symdif.mm"
include "eleq2i.mm"
include "xor.mm"
include "3bitr4i.mm"

theorem elsymdif
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B /_\ C ) <-> -. ( A e. B <-> A e. C ) )

  proof
    cA
    cB
    cC
    cdif
    #
    cC
    cB
    cdif
    #
    cun
    #
    wcel
    #
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    wn
    wa
    #
    @5
    @4
    wn
    wa
    #
    wo
    #
    cA
    cB
    cC
    csymdif
    #
    wcel
    @4
    @5
    wb
    wn
    @3
    cA
    @0
    wcel
    #
    cA
    @1
    wcel
    #
    wo
    @8
    cA
    @0
    @1
    elun
    @10
    @6
    @11
    @7
    cA
    cB
    cC
    eldif
    cA
    cC
    cB
    eldif
    orbi12i
    bitri
    @9
    @2
    cA
    cB
    cC
    df-symdif
    eleq2i
    @4
    @5
    xor
    3bitr4i
end
