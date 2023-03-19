include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "posi.mm"
include "simp3d.mm"

theorem postr
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume posi.b: |- B = ( Base ` K )
  assume posi.l: |- .<_ = ( le ` K )


  assert |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .<_ Y /\ Y .<_ Z ) -> X .<_ Z ) )

  proof
    cK
    cpo
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    wa
    cX
    cX
    c.le
    wbr
    cX
    cY
    c.le
    wbr
    #
    cY
    cX
    c.le
    wbr
    wa
    cX
    cY
    wceq
    wi
    @0
    cY
    cZ
    c.le
    wbr
    wa
    cX
    cZ
    c.le
    wbr
    wi
    cB
    cK
    c.le
    cX
    cY
    cZ
    posi.b
    posi.l
    posi
    simp3d
end
