include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cvv.mm"
include "cs2.mm"
include "wf.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cword.mm"
include "wcel.mm"
include "s2cli.mm"
include "wrdf.mm"
include "ax-mp.mm"
include "c2.mm"
include "wceq.mm"
include "s2len.mm"
include "oveq2.mm"
include "fzo0to2pr.mm"
include "syl6eq.mm"
include "eqcomi.mm"
include "feq2i.mm"
include "mpbir.mm"
include "fdmi.mm"

theorem s2dm
  let cA: class A
  let cB: class B


  assert |- dom <" A B "> = { 0 , 1 }

  proof
    cc0
    c1
    cpr
    #
    cvv
    cA
    cB
    cs2
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
    cB
    s2cli
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
    c2
    wceq
    #
    @3
    @0
    wceq
    cA
    cB
    s2len
    @5
    @3
    cc0
    c2
    cfzo
    co
    @0
    @2
    c2
    cc0
    cfzo
    oveq2
    fzo0to2pr
    syl6eq
    ax-mp
    eqcomi
    feq2i
    mpbir
    fdmi
end
