include "word.mm"
include "csuc.mm"
include "c0.mm"
include "wcel.mm"
include "ordsuc.mm"
include "wne.mm"
include "nsuceq0.mm"
include "ord0eln0.mm"
include "mpbiri.mm"
include "sylbi.mm"

theorem 0elsuc
  let cA: class A


  assert |- ( Ord A -> (/) e. suc A )

  proof
    cA
    word
    cA
    csuc
    #
    word
    #
    c0
    @0
    wcel
    #
    cA
    ordsuc
    @1
    @2
    @0
    c0
    wne
    cA
    nsuceq0
    @0
    ord0eln0
    mpbiri
    sylbi
end
