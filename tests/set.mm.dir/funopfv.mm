include "cop.mm"
include "wcel.mm"
include "wbr.mm"
include "wfun.mm"
include "cfv.mm"
include "wceq.mm"
include "df-br.mm"
include "funbrfv.mm"
include "syl5bir.mm"

theorem funopfv
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( Fun F -> ( <. A , B >. e. F -> ( F ` A ) = B ) )

  proof
    cA
    cB
    cop
    cF
    wcel
    cA
    cB
    cF
    wbr
    cF
    wfun
    cA
    cF
    cfv
    cB
    wceq
    cA
    cB
    cF
    df-br
    cA
    cB
    cF
    funbrfv
    syl5bir
end
