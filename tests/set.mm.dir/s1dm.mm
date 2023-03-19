include "cc0.mm"
include "csn.mm"
include "cvv.mm"
include "cs1.mm"
include "wf.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cword.mm"
include "wcel.mm"
include "s1cli.mm"
include "wrdf.mm"
include "ax-mp.mm"
include "c1.mm"
include "wceq.mm"
include "s1len.mm"
include "oveq2.mm"
include "fzo01.mm"
include "syl6eq.mm"
include "eqcomi.mm"
include "feq2i.mm"
include "mpbir.mm"
include "fdmi.mm"

theorem s1dm
  let cA: class A


  assert |- dom <" A "> = { 0 }

  proof
    cc0
    csn
    #
    cvv
    cA
    cs1
    #
    @0
    cvv
    @1
    wf
    cc0
    @1
    chash
    cfv
    #
    cfzo
    co
    #
    cvv
    @1
    wf
    #
    @1
    cvv
    cword
    wcel
    @4
    cA
    s1cli
    cvv
    @1
    wrdf
    ax-mp
    @0
    @3
    cvv
    @1
    @3
    @0
    @2
    c1
    wceq
    #
    @3
    @0
    wceq
    cA
    s1len
    @5
    @3
    cc0
    c1
    cfzo
    co
    @0
    @2
    c1
    cc0
    cfzo
    oveq2
    fzo01
    syl6eq
    ax-mp
    eqcomi
    feq2i
    mpbir
    fdmi
end
