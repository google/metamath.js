include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "c3.mm"
include "w3o.mm"
include "cfrgr.mm"
include "wcel.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "crusgr.mm"
include "wbr.mm"
include "wa.mm"
include "wo.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "frgrregord013.mm"
include "syl3anc.mm"
include "wi.mm"
include "hasheq0.mm"
include "eqneqall.mm"
include "syl6bi.mm"
include "com23.mm"
include "a1i.mm"
include "3imp.mm"
include "adantr.mm"
include "com12.mm"
include "orc.mm"
include "a1d.mm"
include "olc.mm"
include "3jaoi.mm"
include "mpcom.mm"

theorem frgrregord13
  let cG: class G
  let cK: class K
  let cV: class V
  let vp: setvar p
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  assume frgrreggt1.v: |- V = ( Vtx ` G )


  assert |- ( ( ( G e. FriendGraph /\ V e. Fin /\ V =/= (/) ) /\ G RegUSGraph K ) -> ( ( # ` V ) = 1 \/ ( # ` V ) = 3 ) )

  proof
    cV
    chash
    cfv
    #
    cc0
    wceq
    #
    @0
    c1
    wceq
    #
    @0
    c3
    wceq
    #
    w3o
    #
    cG
    cfrgr
    wcel
    #
    cV
    cfn
    wcel
    #
    cV
    c0
    wne
    #
    w3a
    #
    cG
    cK
    crusgr
    wbr
    #
    wa
    #
    @2
    @3
    wo
    #
    @10
    @5
    @6
    @9
    @4
    @5
    @6
    @7
    @9
    simpl1
    @5
    @6
    @7
    @9
    simpl2
    @8
    @9
    simpr
    cG
    cK
    cV
    frgrreggt1.v
    frgrregord013
    syl3anc
    @1
    @10
    @11
    wi
    @2
    @3
    @10
    @1
    @11
    @8
    @1
    @11
    wi
    #
    @9
    @5
    @6
    @7
    @12
    @6
    @7
    @12
    wi
    wi
    @5
    @6
    @1
    @7
    @11
    @6
    @1
    cV
    c0
    wceq
    @7
    @11
    wi
    cV
    cfn
    hasheq0
    @11
    cV
    c0
    eqneqall
    syl6bi
    com23
    a1i
    3imp
    adantr
    com12
    @2
    @11
    @10
    @2
    @3
    orc
    a1d
    @3
    @11
    @10
    @3
    @2
    olc
    a1d
    3jaoi
    mpcom
end
