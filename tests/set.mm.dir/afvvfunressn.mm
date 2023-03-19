include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "cafv.mm"
include "wcel.mm"
include "wn.mm"
include "cvv.mm"
include "wceq.mm"
include "nfunsnafv.mm"
include "nvelim.mm"
include "syl.mm"
include "con4i.mm"

theorem afvvfunressn
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F ''' A ) e. B -> Fun ( F |` { A } ) )

  proof
    cF
    cA
    csn
    cres
    wfun
    #
    cA
    cF
    cafv
    #
    cB
    wcel
    #
    @0
    wn
    @1
    cvv
    wceq
    @2
    wn
    cA
    cF
    nfunsnafv
    @1
    cB
    nvelim
    syl
    con4i
end
