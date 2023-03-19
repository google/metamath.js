include "c0.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "wceq.mm"
include "s1cli.mm"
include "ccatlid.mm"
include "ax-mp.mm"
include "eqcomi.mm"

theorem s0s1
  let cA: class A


  assert |- <" A "> = ( (/) ++ <" A "> )

  proof
    c0
    cA
    cs1
    #
    cconcat
    co
    #
    @0
    @0
    cvv
    cword
    wcel
    @1
    @0
    wceq
    cA
    s1cli
    cvv
    @0
    ccatlid
    ax-mp
    eqcomi
end
