include "wfun.mm"
include "cdm.mm"
include "wfn.mm"
include "wcel.mm"
include "cafv.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "funfn.mm"
include "fnbrafvb.mm"
include "sylanb.mm"

theorem funbrafvb
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( Fun F /\ A e. dom F ) -> ( ( F ''' A ) = B <-> A F B ) )

  proof
    cF
    wfun
    cF
    cF
    cdm
    #
    wfn
    cA
    @0
    wcel
    cA
    cF
    cafv
    cB
    wceq
    cA
    cB
    cF
    wbr
    wb
    cF
    funfn
    @0
    cA
    cB
    cF
    fnbrafvb
    sylanb
end
