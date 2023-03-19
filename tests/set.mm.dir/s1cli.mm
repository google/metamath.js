include "cs1.mm"
include "cid.mm"
include "cfv.mm"
include "cvv.mm"
include "cword.mm"
include "ids1.mm"
include "wcel.mm"
include "fvex.mm"
include "s1cl.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem s1cli
  let cA: class A


  assert |- <" A "> e. Word _V

  proof
    cA
    cs1
    cA
    cid
    cfv
    #
    cs1
    #
    cvv
    cword
    #
    cA
    ids1
    @0
    cvv
    wcel
    @1
    @2
    wcel
    cA
    cid
    fvex
    @0
    cvv
    s1cl
    ax-mp
    eqeltri
end
