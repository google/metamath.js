include "wfn.mm"
include "wfun.mm"
include "wrel.mm"
include "fnfun.mm"
include "funrel.mm"
include "syl.mm"

theorem fnrel
  let cA: class A
  let cF: class F


  assert |- ( F Fn A -> Rel F )

  proof
    cF
    cA
    wfn
    cF
    wfun
    cF
    wrel
    cA
    cF
    fnfun
    cF
    funrel
    syl
end
