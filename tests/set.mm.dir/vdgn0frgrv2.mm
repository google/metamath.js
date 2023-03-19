include "cfrgr.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cvtxdg.mm"
include "cc0.mm"
include "wne.mm"
include "cconngr.mm"
include "cumgr.mm"
include "wa.mm"
include "wi.mm"
include "frgrconngr.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "usgrumgr.mm"
include "syl.mm"
include "vdn0conngrumgrv2.mm"
include "ex.mm"
include "syl2anc.mm"
include "expdimp.mm"

theorem vdgn0frgrv2
  let cG: class G
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  assume vdn1frgrv2.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FriendGraph /\ N e. V ) -> ( 1 < ( # ` V ) -> ( ( VtxDeg ` G ) ` N ) =/= 0 ) )

  proof
    cG
    cfrgr
    wcel
    #
    cN
    cV
    wcel
    #
    c1
    cV
    chash
    cfv
    clt
    wbr
    #
    cN
    cG
    cvtxdg
    cfv
    cfv
    cc0
    wne
    #
    @0
    cG
    cconngr
    wcel
    #
    cG
    cumgr
    wcel
    #
    @1
    @2
    wa
    #
    @3
    wi
    cG
    frgrconngr
    @0
    cG
    cusgr
    wcel
    @5
    cG
    frgrusgr
    cG
    usgrumgr
    syl
    @4
    @5
    wa
    @6
    @3
    cG
    cN
    cV
    vdn1frgrv2.v
    vdn0conngrumgrv2
    ex
    syl2anc
    expdimp
end
