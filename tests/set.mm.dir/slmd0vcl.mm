include "cslmd.mm"
include "wcel.mm"
include "cmnd.mm"
include "slmdmnd.mm"
include "mndidcl.mm"
include "syl.mm"

theorem slmd0vcl
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume slmd0vcl.v: |- V = ( Base ` W )
  assume slmd0vcl.z: |- .0. = ( 0g ` W )


  assert |- ( W e. SLMod -> .0. e. V )

  proof
    cW
    cslmd
    wcel
    cW
    cmnd
    wcel
    c.0
    cV
    wcel
    cW
    slmdmnd
    cV
    cW
    c.0
    slmd0vcl.v
    slmd0vcl.z
    mndidcl
    syl
end
