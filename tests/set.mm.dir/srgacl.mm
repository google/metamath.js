include "csrg.mm"
include "wcel.mm"
include "cmnd.mm"
include "co.mm"
include "srgmnd.mm"
include "mndcl.mm"
include "syl3an1.mm"

theorem srgacl
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cX: class X
  let cY: class Y
  assume srgacl.b: |- B = ( Base ` R )
  assume srgacl.p: |- .+ = ( +g ` R )


  assert |- ( ( R e. SRing /\ X e. B /\ Y e. B ) -> ( X .+ Y ) e. B )

  proof
    cR
    csrg
    wcel
    cR
    cmnd
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    cX
    cY
    c.pl
    co
    cB
    wcel
    cR
    srgmnd
    cB
    c.pl
    cR
    cX
    cY
    srgacl.b
    srgacl.p
    mndcl
    syl3an1
end
