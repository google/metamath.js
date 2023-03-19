include "cslmd.mm"
include "wcel.mm"
include "csrg.mm"
include "slmdsrg.mm"
include "srgidcl.mm"
include "syl.mm"

theorem slmd1cl
  let c.1: class .1.
  let cF: class F
  let cK: class K
  let cW: class W
  assume slmd1cl.f: |- F = ( Scalar ` W )
  assume slmd1cl.k: |- K = ( Base ` F )
  assume slmd1cl.u: |- .1. = ( 1r ` F )


  assert |- ( W e. SLMod -> .1. e. K )

  proof
    cW
    cslmd
    wcel
    cF
    csrg
    wcel
    c.1
    cK
    wcel
    cF
    cW
    slmd1cl.f
    slmdsrg
    cK
    cF
    c.1
    slmd1cl.k
    slmd1cl.u
    srgidcl
    syl
end
