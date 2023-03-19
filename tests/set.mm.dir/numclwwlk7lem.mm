include "crusgr.mm"
include "wbr.mm"
include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "cfusgr.mm"
include "cn0.mm"
include "finrusgrfusgr.mm"
include "ad2ant2rl.mm"
include "simpll.mm"
include "simprl.mm"
include "frusgrnn0.mm"
include "syl3anc.mm"

theorem numclwwlk7lem
  let cG: class G
  let cK: class K
  let cV: class V
  assume numclwwlk7lem.v: |- V = ( Vtx ` G )


  assert |- ( ( ( G RegUSGraph K /\ G e. FriendGraph ) /\ ( V =/= (/) /\ V e. Fin ) ) -> K e. NN0 )

  proof
    cG
    cK
    crusgr
    wbr
    #
    cG
    cfrgr
    wcel
    #
    wa
    #
    cV
    c0
    wne
    #
    cV
    cfn
    wcel
    #
    wa
    #
    wa
    cG
    cfusgr
    wcel
    #
    @0
    @3
    cK
    cn0
    wcel
    @0
    @4
    @6
    @1
    @3
    cG
    cK
    cV
    numclwwlk7lem.v
    finrusgrfusgr
    ad2ant2rl
    @0
    @1
    @5
    simpll
    @2
    @3
    @4
    simprl
    cG
    cK
    cV
    numclwwlk7lem.v
    frusgrnn0
    syl3anc
end
