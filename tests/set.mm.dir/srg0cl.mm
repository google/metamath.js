include "csrg.mm"
include "wcel.mm"
include "cmnd.mm"
include "srgmnd.mm"
include "mndidcl.mm"
include "syl.mm"

theorem srg0cl
  let cB: class B
  let cR: class R
  let c.0: class .0.
  assume srg0cl.b: |- B = ( Base ` R )
  assume srg0cl.z: |- .0. = ( 0g ` R )


  assert |- ( R e. SRing -> .0. e. B )

  proof
    cR
    csrg
    wcel
    cR
    cmnd
    wcel
    c.0
    cB
    wcel
    cR
    srgmnd
    cB
    cR
    c.0
    srg0cl.b
    srg0cl.z
    mndidcl
    syl
end
