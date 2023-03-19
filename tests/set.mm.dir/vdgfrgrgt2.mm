include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cvtxdg.mm"
include "cle.mm"
include "cc0.mm"
include "wne.mm"
include "vdgn0frgrv2.mm"
include "imp.mm"
include "vdgn1frgrv2.mm"
include "wb.mm"
include "cxnn0.mm"
include "vtxdgelxnn0.mm"
include "xnn0n0n1ge2b.mm"
include "syl.mm"
include "ad2antlr.mm"
include "mpbi2and.mm"
include "ex.mm"

theorem vdgfrgrgt2
  let cG: class G
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vi: setvar i
  let vv: setvar v
  assume vdn1frgrv2.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FriendGraph /\ N e. V ) -> ( 1 < ( # ` V ) -> 2 <_ ( ( VtxDeg ` G ) ` N ) ) )

  proof
    cG
    cfrgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    c1
    cV
    chash
    cfv
    clt
    wbr
    #
    c2
    cN
    cG
    cvtxdg
    cfv
    cfv
    #
    cle
    wbr
    #
    @2
    @3
    wa
    @4
    cc0
    wne
    #
    @4
    c1
    wne
    #
    @5
    @2
    @3
    @6
    cG
    cN
    cV
    vdn1frgrv2.v
    vdgn0frgrv2
    imp
    @2
    @3
    @7
    cG
    cN
    cV
    vdn1frgrv2.v
    vdgn1frgrv2
    imp
    @1
    @6
    @7
    wa
    @5
    wb
    #
    @0
    @3
    @1
    @4
    cxnn0
    wcel
    @8
    cG
    cV
    cN
    vdn1frgrv2.v
    vtxdgelxnn0
    @4
    xnn0n0n1ge2b
    syl
    ad2antlr
    mpbi2and
    ex
end
