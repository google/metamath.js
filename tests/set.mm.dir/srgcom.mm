include "csrg.mm"
include "wcel.mm"
include "ccmn.mm"
include "co.mm"
include "wceq.mm"
include "srgcmn.mm"
include "cmncom.mm"
include "syl3an1.mm"

theorem srgcom
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cX: class X
  let cY: class Y
  assume srgacl.b: |- B = ( Base ` R )
  assume srgacl.p: |- .+ = ( +g ` R )


  assert |- ( ( R e. SRing /\ X e. B /\ Y e. B ) -> ( X .+ Y ) = ( Y .+ X ) )

  proof
    cR
    csrg
    wcel
    cR
    ccmn
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
    cY
    cX
    c.pl
    co
    wceq
    cR
    srgcmn
    cB
    c.pl
    cR
    cX
    cY
    srgacl.b
    srgacl.p
    cmncom
    syl3an1
end
