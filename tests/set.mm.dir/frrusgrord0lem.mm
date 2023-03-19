include "cfrgr.mm"
include "wcel.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cc.mm"
include "chash.mm"
include "cc0.mm"
include "cn0.mm"
include "cfusgr.mm"
include "wi.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "anim1i.mm"
include "isfusgr.mm"
include "sylibr.mm"
include "eqid.mm"
include "fusgrregdegfi.mm"
include "stoic3.mm"
include "imp.mm"
include "nn0cnd.mm"
include "hashcl.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "hasheq0.mm"
include "biimpd.mm"
include "necon3d.mm"
include "3adant1.mm"
include "3jca.mm"

theorem frrusgrord0lem
  let vv: setvar v
  let cG: class G
  let cK: class K
  let cV: class V
  assume frrusgrord0.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint K v
  disjoint V v
  assert |- ( ( ( G e. FriendGraph /\ V e. Fin /\ V =/= (/) ) /\ A. v e. V ( ( VtxDeg ` G ) ` v ) = K ) -> ( K e. CC /\ ( # ` V ) e. CC /\ ( # ` V ) =/= 0 ) )

  proof
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
    vv
    cv
    cG
    cvtxdg
    cfv
    #
    cfv
    cK
    wceq
    vv
    cV
    wral
    #
    wa
    #
    cK
    cc
    wcel
    cV
    chash
    cfv
    #
    cc
    wcel
    #
    @7
    cc0
    wne
    #
    @6
    cK
    @3
    @5
    cK
    cn0
    wcel
    #
    @0
    @1
    cG
    cfusgr
    wcel
    #
    @2
    @5
    @10
    wi
    @0
    @1
    wa
    cG
    cusgr
    wcel
    #
    @1
    wa
    @11
    @0
    @12
    @1
    cG
    frgrusgr
    anim1i
    cG
    cV
    frrusgrord0.v
    isfusgr
    sylibr
    vv
    @4
    cG
    cK
    cV
    frrusgrord0.v
    @4
    eqid
    fusgrregdegfi
    stoic3
    imp
    nn0cnd
    @3
    @8
    @5
    @1
    @0
    @8
    @2
    @1
    @7
    cV
    hashcl
    nn0cnd
    3ad2ant2
    adantr
    @3
    @9
    @5
    @1
    @2
    @9
    @0
    @1
    @2
    @9
    @1
    @7
    cc0
    cV
    c0
    @1
    @7
    cc0
    wceq
    cV
    c0
    wceq
    cV
    cfn
    hasheq0
    biimpd
    necon3d
    imp
    3adant1
    adantr
    3jca
end
