include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wceq.mm"
include "chash.mm"
include "cfv.mm"
include "fveq2.mm"
include "hashfz1.mm"
include "eqeqan12d.mm"
include "syl5ib.mm"
include "oveq2.mm"
include "impbid1.mm"

theorem fz1eqb
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( ( 1 ... M ) = ( 1 ... N ) <-> M = N ) )

  proof
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    c1
    cM
    cfz
    co
    #
    c1
    cN
    cfz
    co
    #
    wceq
    #
    cM
    cN
    wceq
    #
    @5
    @3
    chash
    cfv
    #
    @4
    chash
    cfv
    #
    wceq
    @2
    @6
    @3
    @4
    chash
    fveq2
    @0
    @1
    @7
    cM
    @8
    cN
    cM
    hashfz1
    cN
    hashfz1
    eqeqan12d
    syl5ib
    cM
    cN
    c1
    cfz
    oveq2
    impbid1
end
