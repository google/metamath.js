include "wcel.mm"
include "cs1.mm"
include "crn.mm"
include "cc0.mm"
include "cop.mm"
include "csn.mm"
include "s1val.mm"
include "rneqd.mm"
include "c0ex.mm"
include "rnsnop.mm"
include "syl6eq.mm"

theorem s1rn
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ran <" A "> = { A } )

  proof
    cA
    cV
    wcel
    #
    cA
    cs1
    #
    crn
    cc0
    cA
    cop
    csn
    #
    crn
    cA
    csn
    @0
    @1
    @2
    cA
    cV
    s1val
    rneqd
    cc0
    cA
    c0ex
    rnsnop
    syl6eq
end
