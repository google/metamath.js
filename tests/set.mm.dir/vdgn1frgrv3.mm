include "cfrgr.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cvtxdg.mm"
include "wne.mm"
include "vdgn1frgrv2.mm"
include "impancom.mm"
include "ralrimiv.mm"

theorem vdgn1frgrv3
  let vv: setvar v
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let cN: class N
  let vi: setvar i
  assume vdn1frgrv2.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint V v
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint b c
  disjoint b x
  disjoint c x
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N x
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V x
  disjoint G i
  disjoint i x
  disjoint N i
  assert |- ( ( G e. FriendGraph /\ 1 < ( # ` V ) ) -> A. v e. V ( ( VtxDeg ` G ) ` v ) =/= 1 )

  proof
    cG
    cfrgr
    wcel
    #
    c1
    cV
    chash
    cfv
    clt
    wbr
    #
    wa
    vv
    cv
    #
    cG
    cvtxdg
    cfv
    cfv
    c1
    wne
    #
    vv
    cV
    @0
    @2
    cV
    wcel
    @1
    @3
    cG
    @2
    cV
    vdn1frgrv2.v
    vdgn1frgrv2
    impancom
    ralrimiv
end
