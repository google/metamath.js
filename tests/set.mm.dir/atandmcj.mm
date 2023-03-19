include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cc.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "wne.mm"
include "atandm3.mm"
include "simplbi.mm"
include "cjcld.mm"
include "cn0.mm"
include "wceq.mm"
include "2nn0.mm"
include "cjexp.mm"
include "sylancl.mm"
include "sqcld.mm"
include "cjcjd.mm"
include "simprbi.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "cr.mm"
include "neg1rr.mm"
include "cjre.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "syl.mm"
include "eqnetrrd.mm"
include "sylanbrc.mm"

theorem atandmcj
  let cA: class A


  assert |- ( A e. dom arctan -> ( * ` A ) e. dom arctan )

  proof
    cA
    catan
    cdm
    #
    wcel
    #
    cA
    ccj
    cfv
    #
    cc
    wcel
    @2
    c2
    cexp
    co
    #
    c1
    cneg
    #
    wne
    @2
    @0
    wcel
    @1
    cA
    @1
    cA
    cc
    wcel
    #
    cA
    c2
    cexp
    co
    #
    @4
    wne
    #
    cA
    atandm3
    #
    simplbi
    #
    cjcld
    @1
    @6
    ccj
    cfv
    #
    @3
    @4
    @1
    @5
    c2
    cn0
    wcel
    @10
    @3
    wceq
    @9
    2nn0
    cA
    c2
    cjexp
    sylancl
    @1
    @10
    ccj
    cfv
    #
    @4
    wne
    @10
    @4
    wne
    @1
    @11
    @6
    @4
    @1
    @6
    @1
    cA
    @9
    sqcld
    cjcjd
    @1
    @5
    @7
    @8
    simprbi
    eqnetrd
    @10
    @4
    @11
    @4
    @10
    @4
    wceq
    @11
    @4
    ccj
    cfv
    #
    @4
    @10
    @4
    ccj
    fveq2
    @4
    cr
    wcel
    @12
    @4
    wceq
    neg1rr
    @4
    cjre
    ax-mp
    syl6eq
    necon3i
    syl
    eqnetrrd
    @2
    atandm3
    sylanbrc
end
