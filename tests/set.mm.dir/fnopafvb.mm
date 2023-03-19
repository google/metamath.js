include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cafv.mm"
include "wceq.mm"
include "wbr.mm"
include "cop.mm"
include "fnbrafvb.mm"
include "df-br.mm"
include "syl6bb.mm"

theorem fnopafvb
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F Fn A /\ B e. A ) -> ( ( F ''' B ) = C <-> <. B , C >. e. F ) )

  proof
    cF
    cA
    wfn
    cB
    cA
    wcel
    wa
    cB
    cF
    cafv
    cC
    wceq
    cB
    cC
    cF
    wbr
    cB
    cC
    cop
    cF
    wcel
    cA
    cB
    cC
    cF
    fnbrafvb
    cB
    cC
    cF
    df-br
    syl6bb
end
