include "clmod.mm"
include "wcel.mm"
include "crg.mm"
include "lmodring.mm"
include "ring0cl.mm"
include "syl.mm"

theorem lmod0cl
  let cF: class F
  let cK: class K
  let cW: class W
  let c.0: class .0.
  assume lmod0cl.f: |- F = ( Scalar ` W )
  assume lmod0cl.k: |- K = ( Base ` F )
  assume lmod0cl.z: |- .0. = ( 0g ` F )


  assert |- ( W e. LMod -> .0. e. K )

  proof
    cW
    clmod
    wcel
    cF
    crg
    wcel
    c.0
    cK
    wcel
    cF
    cW
    lmod0cl.f
    lmodring
    cK
    cF
    c.0
    lmod0cl.k
    lmod0cl.z
    ring0cl
    syl
end
