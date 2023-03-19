include "wfun.mm"
include "cdm.mm"
include "wfn.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cop.mm"
include "wb.mm"
include "funfn.mm"
include "fnopfvb.mm"
include "sylanb.mm"

theorem funopfvb
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ A e. dom F ) -> ( ( F ` A ) = B <-> <. A , B >. e. F ) )

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
    cfv
    cB
    wceq
    cA
    cB
    cop
    cF
    wcel
    wb
    cF
    funfn
    @0
    cA
    cB
    cF
    fnopfvb
    sylanb
end
