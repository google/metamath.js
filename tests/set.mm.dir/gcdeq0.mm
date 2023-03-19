include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "gcdn0cl.mm"
include "nnne0d.mm"
include "ex.mm"
include "necon4bd.mm"
include "oveq12.mm"
include "gcd0val.mm"
include "syl6eq.mm"
include "impbid1.mm"

theorem gcdeq0
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( ( M gcd N ) = 0 <-> ( M = 0 /\ N = 0 ) ) )

  proof
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    #
    cM
    cN
    cgcd
    co
    #
    cc0
    wceq
    cM
    cc0
    wceq
    cN
    cc0
    wceq
    wa
    #
    @0
    @2
    @1
    cc0
    @0
    @2
    wn
    #
    @1
    cc0
    wne
    @0
    @3
    wa
    @1
    cM
    cN
    gcdn0cl
    nnne0d
    ex
    necon4bd
    @2
    @1
    cc0
    cc0
    cgcd
    co
    cc0
    cM
    cc0
    cN
    cc0
    cgcd
    oveq12
    gcd0val
    syl6eq
    impbid1
end
