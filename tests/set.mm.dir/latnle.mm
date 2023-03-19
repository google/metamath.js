include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wne.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "latlej1.mm"
include "biantrurd.mm"
include "wceq.mm"
include "wb.mm"
include "latleeqj1.mm"
include "3com23.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "latjcom.mm"
include "eqeq2d.mm"
include "bitr4d.mm"
include "necon3bbid.mm"
include "latjcl.mm"
include "pltval.mm"
include "syld3an3.mm"
include "3bitr4d.mm"

theorem latnle
  let cB: class B
  let c.lt: class .<
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume latnle.b: |- B = ( Base ` K )
  assume latnle.l: |- .<_ = ( le ` K )
  assume latnle.s: |- .< = ( lt ` K )
  assume latnle.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( -. Y .<_ X <-> X .< ( X .\/ Y ) ) )

  proof
    cK
    clat
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cX
    cY
    c.or
    co
    #
    wne
    #
    cX
    @4
    c.le
    wbr
    #
    @5
    wa
    #
    cY
    cX
    c.le
    wbr
    #
    wn
    cX
    @4
    c.lt
    wbr
    #
    @3
    @6
    @5
    cB
    c.or
    cK
    c.le
    cX
    cY
    latnle.b
    latnle.l
    latnle.j
    latlej1
    biantrurd
    @3
    @8
    cX
    @4
    @3
    @8
    cX
    cY
    cX
    c.or
    co
    #
    wceq
    #
    cX
    @4
    wceq
    @3
    @8
    @10
    cX
    wceq
    #
    @11
    @0
    @2
    @1
    @8
    @12
    wb
    cB
    c.or
    cK
    c.le
    cY
    cX
    latnle.b
    latnle.l
    latnle.j
    latleeqj1
    3com23
    @10
    cX
    eqcom
    syl6bb
    @3
    @4
    @10
    cX
    cB
    c.or
    cK
    cX
    cY
    latnle.b
    latnle.j
    latjcom
    eqeq2d
    bitr4d
    necon3bbid
    @0
    @1
    @2
    @4
    cB
    wcel
    @9
    @7
    wb
    cB
    c.or
    cK
    cX
    cY
    latnle.b
    latnle.j
    latjcl
    clat
    cB
    cB
    c.lt
    cK
    c.le
    cX
    @4
    latnle.l
    latnle.s
    pltval
    syld3an3
    3bitr4d
end
