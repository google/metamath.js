include "ccrg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "crngcom.mm"
include "opprmul.mm"
include "syl6eqr.mm"

theorem crngoppr
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cO: class O
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume opprval.1: |- B = ( Base ` R )
  assume opprval.2: |- .x. = ( .r ` R )
  assume opprval.3: |- O = ( oppR ` R )
  assume opprmulfval.4: |- .xb = ( .r ` O )


  assert |- ( ( R e. CRing /\ X e. B /\ Y e. B ) -> ( X .x. Y ) = ( X .xb Y ) )

  proof
    cR
    ccrg
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    w3a
    cX
    cY
    c.x
    co
    cY
    cX
    c.x
    co
    cX
    cY
    c.xb
    co
    cB
    cR
    c.x
    cX
    cY
    opprval.1
    opprval.2
    crngcom
    cB
    cR
    c.xb
    c.x
    cO
    cX
    cY
    opprval.1
    opprval.2
    opprval.3
    opprmulfval.4
    opprmul
    syl6eqr
end
