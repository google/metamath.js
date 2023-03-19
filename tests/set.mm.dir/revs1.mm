include "cc0.mm"
include "cs1.mm"
include "creverse.mm"
include "cfv.mm"
include "cid.mm"
include "wceq.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "cfzo.mm"
include "s1cli.mm"
include "cn.mm"
include "s1len.mm"
include "1nn.mm"
include "eqeltri.mm"
include "lbfzo0.mm"
include "mpbir.mm"
include "revfv.mm"
include "mp2an.mm"
include "oveq1i.mm"
include "1m1e0.mm"
include "eqtri.mm"
include "0m0e0.mm"
include "fveq2i.mm"
include "ids1.mm"
include "fveq1i.mm"
include "fvex.mm"
include "s1fv.mm"
include "ax-mp.mm"
include "s1eq.mm"
include "revcl.mm"
include "revlen.mm"
include "eqs1.mm"
include "3eqtr4i.mm"

theorem revs1
  let cS: class S
  let vw: setvar w
  let vx: setvar x
  let cW: class W
  let cA: class A
  let cX: class X
  let cT: class T


  assert |- ( reverse ` <" S "> ) = <" S ">

  proof
    cc0
    cS
    cs1
    #
    creverse
    cfv
    #
    cfv
    #
    cs1
    #
    cS
    cid
    cfv
    #
    cs1
    #
    @1
    @0
    @2
    @4
    wceq
    @3
    @5
    wceq
    @2
    @0
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cc0
    cmin
    co
    #
    @0
    cfv
    #
    @4
    @0
    cvv
    cword
    #
    wcel
    #
    cc0
    cc0
    @6
    cfzo
    co
    wcel
    #
    @2
    @9
    wceq
    cS
    s1cli
    #
    @12
    @6
    cn
    wcel
    @6
    c1
    cn
    cS
    s1len
    #
    1nn
    eqeltri
    @6
    lbfzo0
    mpbir
    cvv
    @0
    cc0
    revfv
    mp2an
    @9
    cc0
    @0
    cfv
    #
    @4
    @8
    cc0
    @0
    @8
    cc0
    cc0
    cmin
    co
    cc0
    @7
    cc0
    cc0
    cmin
    @7
    c1
    c1
    cmin
    co
    cc0
    @6
    c1
    c1
    cmin
    @14
    oveq1i
    1m1e0
    eqtri
    oveq1i
    0m0e0
    eqtri
    fveq2i
    @15
    cc0
    @5
    cfv
    #
    @4
    cc0
    @0
    @5
    cS
    ids1
    #
    fveq1i
    @4
    cvv
    wcel
    @16
    @4
    wceq
    cS
    cid
    fvex
    @4
    cvv
    s1fv
    ax-mp
    eqtri
    eqtri
    eqtri
    @2
    @4
    s1eq
    ax-mp
    @1
    @10
    wcel
    #
    @1
    chash
    cfv
    #
    c1
    wceq
    @1
    @3
    wceq
    @11
    @18
    @13
    cvv
    @0
    revcl
    ax-mp
    @19
    @6
    c1
    @11
    @19
    @6
    wceq
    @13
    cvv
    @0
    revlen
    ax-mp
    @14
    eqtri
    cvv
    @1
    eqs1
    mp2an
    @17
    3eqtr4i
end
