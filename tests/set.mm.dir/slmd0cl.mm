include "cslmd.mm"
include "wcel.mm"
include "csrg.mm"
include "slmdsrg.mm"
include "srg0cl.mm"
include "syl.mm"

theorem slmd0cl
  let cF: class F
  let cK: class K
  let cW: class W
  let c.0: class .0.
  assume slmd0cl.f: |- F = ( Scalar ` W )
  assume slmd0cl.k: |- K = ( Base ` F )
  assume slmd0cl.z: |- .0. = ( 0g ` F )


  assert |- ( W e. SLMod -> .0. e. K )

  proof
    cW
    cslmd
    wcel
    cF
    csrg
    wcel
    c.0
    cK
    wcel
    cF
    cW
    slmd0cl.f
    slmdsrg
    cK
    cF
    c.0
    slmd0cl.k
    slmd0cl.z
    srg0cl
    syl
end
