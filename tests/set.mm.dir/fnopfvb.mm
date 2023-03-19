include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "cop.mm"
include "fnbrfvb.mm"
include "df-br.mm"
include "syl6bb.mm"

theorem fnopfvb
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F Fn A /\ B e. A ) -> ( ( F ` B ) = C <-> <. B , C >. e. F ) )

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
    cfv
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
    fnbrfvb
    cB
    cC
    cF
    df-br
    syl6bb
end
