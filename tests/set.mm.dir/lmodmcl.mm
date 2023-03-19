include "clmod.mm"
include "wcel.mm"
include "crg.mm"
include "co.mm"
include "lmodring.mm"
include "ringcl.mm"
include "syl3an1.mm"

theorem lmodmcl
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lmodmcl.f: |- F = ( Scalar ` W )
  assume lmodmcl.k: |- K = ( Base ` F )
  assume lmodmcl.t: |- .x. = ( .r ` F )


  assert |- ( ( W e. LMod /\ X e. K /\ Y e. K ) -> ( X .x. Y ) e. K )

  proof
    cW
    clmod
    wcel
    cF
    crg
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
    lmodmcl.f
    lmodring
    cK
    cF
    c.x
    cX
    cY
    lmodmcl.k
    lmodmcl.t
    ringcl
    syl3an1
end
