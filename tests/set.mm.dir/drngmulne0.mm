include "co.mm"
include "wne.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "drngmul0or.mm"
include "necon3abid.mm"
include "neanior.mm"
include "syl6bbr.mm"

theorem drngmulne0
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume drngmuleq0.b: |- B = ( Base ` R )
  assume drngmuleq0.o: |- .0. = ( 0g ` R )
  assume drngmuleq0.t: |- .x. = ( .r ` R )
  assume drngmuleq0.r: |- ( ph -> R e. DivRing )
  assume drngmuleq0.x: |- ( ph -> X e. B )
  assume drngmuleq0.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( ( X .x. Y ) =/= .0. <-> ( X =/= .0. /\ Y =/= .0. ) ) )

  proof
    wph
    cX
    cY
    c.x
    co
    #
    c.0
    wne
    cX
    c.0
    wceq
    cY
    c.0
    wceq
    wo
    #
    wn
    cX
    c.0
    wne
    cY
    c.0
    wne
    wa
    wph
    @1
    @0
    c.0
    wph
    cB
    cR
    c.x
    cX
    cY
    c.0
    drngmuleq0.b
    drngmuleq0.o
    drngmuleq0.t
    drngmuleq0.r
    drngmuleq0.x
    drngmuleq0.y
    drngmul0or
    necon3abid
    cX
    c.0
    cY
    c.0
    neanior
    syl6bbr
end
