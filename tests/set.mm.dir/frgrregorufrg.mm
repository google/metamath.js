include "cfrgr.mm"
include "wcel.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "crusgr.mm"
include "wbr.mm"
include "cpr.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wo.mm"
include "wi.mm"
include "cn0.mm"
include "wa.mm"
include "eqid.mm"
include "frgrregorufr.mm"
include "adantr.mm"
include "cusgr.mm"
include "cxnn0.mm"
include "frgrusgr.mm"
include "nn0xnn0.mm"
include "usgreqdrusgr.mm"
include "3expia.mm"
include "syl2an.mm"
include "orim1d.mm"
include "syld.mm"
include "ralrimiva.mm"

theorem frgrregorufrg
  let vw: setvar w
  let vv: setvar v
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cV: class V
  let va: setvar a
  assume frgrregorufrg.v: |- V = ( Vtx ` G )
  assume frgrregorufrg.e: |- E = ( Edg ` G )

  disjoint G a
  disjoint G k
  disjoint G v
  disjoint G w
  disjoint v w
  disjoint E a
  disjoint E v
  disjoint a v
  disjoint V a
  disjoint V v
  disjoint V w
  disjoint a w
  disjoint a k
  disjoint k v
  disjoint k w
  assert |- ( G e. FriendGraph -> A. k e. NN0 ( E. a e. V ( ( VtxDeg ` G ) ` a ) = k -> ( G RegUSGraph k \/ E. v e. V A. w e. ( V \ { v } ) { v , w } e. E ) ) )

  proof
    cG
    cfrgr
    wcel
    #
    va
    cv
    cG
    cvtxdg
    cfv
    #
    cfv
    vk
    cv
    #
    wceq
    va
    cV
    wrex
    #
    cG
    @2
    crusgr
    wbr
    #
    vv
    cv
    #
    vw
    cv
    cpr
    cE
    wcel
    vw
    cV
    @5
    csn
    cdif
    wral
    vv
    cV
    wrex
    #
    wo
    #
    wi
    vk
    cn0
    @0
    @2
    cn0
    wcel
    #
    wa
    #
    @3
    @5
    @1
    cfv
    @2
    wceq
    vv
    cV
    wral
    #
    @6
    wo
    #
    @7
    @0
    @3
    @11
    wi
    @8
    vw
    vv
    @1
    cE
    cG
    @2
    cV
    va
    frgrregorufrg.v
    frgrregorufrg.e
    @1
    eqid
    #
    frgrregorufr
    adantr
    @9
    @10
    @4
    @6
    @0
    cG
    cusgr
    wcel
    #
    @2
    cxnn0
    wcel
    #
    @10
    @4
    wi
    @8
    cG
    frgrusgr
    @2
    nn0xnn0
    @13
    @14
    @10
    @4
    vv
    @1
    cG
    @2
    cV
    frgrregorufrg.v
    @12
    usgreqdrusgr
    3expia
    syl2an
    orim1d
    syld
    ralrimiva
end
