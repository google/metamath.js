include "cslmd.mm"
include "wcel.mm"
include "cmnd.mm"
include "co.mm"
include "csrg.mm"
include "slmdsrg.mm"
include "srgmnd.mm"
include "syl.mm"
include "mndcl.mm"
include "syl3an1.mm"

theorem slmdacl
  let c.pl: class .+
  let cF: class F
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume slmdacl.f: |- F = ( Scalar ` W )
  assume slmdacl.k: |- K = ( Base ` F )
  assume slmdacl.p: |- .+ = ( +g ` F )


  assert |- ( ( W e. SLMod /\ X e. K /\ Y e. K ) -> ( X .+ Y ) e. K )

  proof
    cW
    cslmd
    wcel
    #
    cF
    cmnd
    wcel
    #
    cX
    cK
    wcel
    cY
    cK
    wcel
    cX
    cY
    c.pl
    co
    cK
    wcel
    @0
    cF
    csrg
    wcel
    @1
    cF
    cW
    slmdacl.f
    slmdsrg
    cF
    srgmnd
    syl
    cK
    c.pl
    cF
    cX
    cY
    slmdacl.k
    slmdacl.p
    mndcl
    syl3an1
end
