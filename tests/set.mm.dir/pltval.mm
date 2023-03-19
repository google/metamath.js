include "wcel.mm"
include "wbr.mm"
include "wne.mm"
include "wa.mm"
include "wb.mm"
include "cid.mm"
include "cdif.mm"
include "pltfval.mm"
include "breqd.mm"
include "wn.mm"
include "brdif.mm"
include "ideqg.mm"
include "necon3bbid.mm"
include "adantl.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "sylan9bb.mm"
include "3impb.mm"

theorem pltval
  let cA: class A
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume pltval.l: |- .<_ = ( le ` K )
  assume pltval.s: |- .< = ( lt ` K )


  assert |- ( ( K e. A /\ X e. B /\ Y e. C ) -> ( X .< Y <-> ( X .<_ Y /\ X =/= Y ) ) )

  proof
    cK
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cC
    wcel
    #
    cX
    cY
    c.lt
    wbr
    #
    cX
    cY
    c.le
    wbr
    #
    cX
    cY
    wne
    #
    wa
    #
    wb
    @0
    @3
    cX
    cY
    c.le
    cid
    cdif
    #
    wbr
    #
    @1
    @2
    wa
    #
    @6
    @0
    c.lt
    @7
    cX
    cY
    cA
    c.lt
    cK
    c.le
    pltval.l
    pltval.s
    pltfval
    breqd
    @8
    @4
    cX
    cY
    cid
    wbr
    #
    wn
    #
    wa
    @9
    @6
    cX
    cY
    c.le
    cid
    brdif
    @9
    @11
    @5
    @4
    @2
    @11
    @5
    wb
    @1
    @2
    @10
    cX
    cY
    cX
    cY
    cC
    ideqg
    necon3bbid
    adantl
    anbi2d
    syl5bb
    sylan9bb
    3impb
end
