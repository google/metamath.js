include "ctos.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cpo.mm"
include "wb.mm"
include "tospos.mm"
include "pltval3.mm"
include "syl3an1.mm"
include "wo.mm"
include "tleile.mm"
include "ibar.mm"
include "pm5.61.mm"
include "syl6rbb.mm"
include "syl.mm"
include "bitrd.mm"

theorem tltnle
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume tleile.b: |- B = ( Base ` K )
  assume tleile.l: |- .<_ = ( le ` K )
  assume tltnle.s: |- .< = ( lt ` K )


  assert |- ( ( K e. Toset /\ X e. B /\ Y e. B ) -> ( X .< Y <-> -. Y .<_ X ) )

  proof
    cK
    ctos
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
    cY
    c.lt
    wbr
    #
    cX
    cY
    c.le
    wbr
    #
    cY
    cX
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @7
    @0
    cK
    cpo
    wcel
    @1
    @2
    @4
    @8
    wb
    cK
    tospos
    cB
    c.lt
    cK
    c.le
    cX
    cY
    tleile.b
    tleile.l
    tltnle.s
    pltval3
    syl3an1
    @3
    @5
    @6
    wo
    #
    @8
    @7
    wb
    cB
    cK
    c.le
    cX
    cY
    tleile.b
    tleile.l
    tleile
    @9
    @7
    @9
    @7
    wa
    @8
    @9
    @7
    ibar
    @5
    @6
    pm5.61
    syl6rbb
    syl
    bitrd
end
