include "cnbgr.mm"
include "co.mm"
include "wcel.mm"
include "wn.mm"
include "wnel.mm"
include "df-nel.mm"
include "eleq2i.mm"
include "xchbinx.mm"
include "sylib.mm"
include "nbgrsym.mm"
include "sylnibr.mm"
include "wceq.mm"
include "wb.mm"
include "neleq2.mm"
include "ax-mp.mm"
include "bitri.mm"
include "sylibr.mm"

theorem frgrncvvdeqlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  assume frgrncvvdeq.v1: |- V = ( Vtx ` G )
  assume frgrncvvdeq.e: |- E = ( Edg ` G )
  assume frgrncvvdeq.nx: |- D = ( G NeighbVtx X )
  assume frgrncvvdeq.ny: |- N = ( G NeighbVtx Y )
  assume frgrncvvdeq.x: |- ( ph -> X e. V )
  assume frgrncvvdeq.y: |- ( ph -> Y e. V )
  assume frgrncvvdeq.ne: |- ( ph -> X =/= Y )
  assume frgrncvvdeq.xy: |- ( ph -> Y e/ D )
  assume frgrncvvdeq.f: |- ( ph -> G e. FriendGraph )
  assume frgrncvvdeq.a: |- A = ( x e. D |-> ( iota_ y e. N { x , y } e. E ) )


  assert |- ( ph -> X e/ N )

  proof
    wph
    cX
    cG
    cY
    cnbgr
    co
    #
    wcel
    #
    wn
    #
    cX
    cN
    wnel
    #
    wph
    cY
    cG
    cX
    cnbgr
    co
    #
    wcel
    #
    @1
    wph
    cY
    cD
    wnel
    #
    @5
    wn
    frgrncvvdeq.xy
    @6
    cY
    cD
    wcel
    @5
    cY
    cD
    df-nel
    cD
    @4
    cY
    frgrncvvdeq.nx
    eleq2i
    xchbinx
    sylib
    cG
    cY
    cX
    nbgrsym
    sylnibr
    @3
    cX
    @0
    wnel
    #
    @2
    cN
    @0
    wceq
    @3
    @7
    wb
    frgrncvvdeq.ny
    cN
    @0
    cX
    neleq2
    ax-mp
    cX
    @0
    df-nel
    bitri
    sylibr
end
