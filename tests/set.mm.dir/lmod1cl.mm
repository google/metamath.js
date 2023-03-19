include "clmod.mm"
include "wcel.mm"
include "crg.mm"
include "lmodring.mm"
include "ringidcl.mm"
include "syl.mm"

theorem lmod1cl
  let c.1: class .1.
  let cF: class F
  let cK: class K
  let cW: class W
  assume lmod1cl.f: |- F = ( Scalar ` W )
  assume lmod1cl.k: |- K = ( Base ` F )
  assume lmod1cl.u: |- .1. = ( 1r ` F )


  assert |- ( W e. LMod -> .1. e. K )

  proof
    cW
    clmod
    wcel
    cF
    crg
    wcel
    c.1
    cK
    wcel
    cF
    cW
    lmod1cl.f
    lmodring
    cK
    cF
    c.1
    lmod1cl.k
    lmod1cl.u
    ringidcl
    syl
end
