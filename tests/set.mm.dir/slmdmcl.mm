include "cslmd.mm"
include "wcel.mm"
include "csrg.mm"
include "co.mm"
include "slmdsrg.mm"
include "srgcl.mm"
include "syl3an1.mm"

theorem slmdmcl
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume slmdmcl.f: |- F = ( Scalar ` W )
  assume slmdmcl.k: |- K = ( Base ` F )
  assume slmdmcl.t: |- .x. = ( .r ` F )


  assert |- ( ( W e. SLMod /\ X e. K /\ Y e. K ) -> ( X .x. Y ) e. K )

  proof
    cW
    cslmd
    wcel
    cF
    csrg
    wcel
    cX
    cK
    wcel
    cY
    cK
    wcel
    cX
    cY
    c.x
    co
    cK
    wcel
    cF
    cW
    slmdmcl.f
    slmdsrg
    cK
    cF
    c.x
    cX
    cY
    slmdmcl.k
    slmdmcl.t
    srgcl
    syl3an1
end
