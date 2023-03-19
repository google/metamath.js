include "csrg.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "srgi.mm"
include "simprd.mm"

theorem srgdir
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume srgdi.b: |- B = ( Base ` R )
  assume srgdi.p: |- .+ = ( +g ` R )
  assume srgdi.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. SRing /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .+ Y ) .x. Z ) = ( ( X .x. Z ) .+ ( Y .x. Z ) ) )

  proof
    cR
    csrg
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
    cY
    cZ
    c.pl
    co
    c.x
    co
    cX
    cY
    c.x
    co
    cX
    cZ
    c.x
    co
    #
    c.pl
    co
    wceq
    cX
    cY
    c.pl
    co
    cZ
    c.x
    co
    @0
    cY
    cZ
    c.x
    co
    c.pl
    co
    wceq
    cB
    c.pl
    cR
    c.x
    cX
    cY
    cZ
    srgdi.b
    srgdi.p
    srgdi.t
    srgi
    simprd
end
