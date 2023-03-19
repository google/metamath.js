include "wcel.mm"
include "cs1.mm"
include "cc0.mm"
include "cop.mm"
include "csn.mm"
include "cword.mm"
include "s1val.mm"
include "snopiswrd.mm"
include "eqeltrd.mm"

theorem s1cl
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> <" A "> e. Word B )

  proof
    cA
    cB
    wcel
    cA
    cs1
    cc0
    cA
    cop
    csn
    cB
    cword
    cA
    cB
    s1val
    cA
    cB
    snopiswrd
    eqeltrd
end
