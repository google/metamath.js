include "cslmd.mm"
include "wcel.mm"
include "cmnd.mm"
include "c0g.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "slmdmnd.mm"
include "eqid.mm"
include "mndidcl.mm"
include "ne0i.mm"
include "3syl.mm"

theorem slmdbn0
  let cB: class B
  let cW: class W
  assume slmdbn0.b: |- B = ( Base ` W )


  assert |- ( W e. SLMod -> B =/= (/) )

  proof
    cW
    cslmd
    wcel
    cW
    cmnd
    wcel
    cW
    c0g
    cfv
    #
    cB
    wcel
    cB
    c0
    wne
    cW
    slmdmnd
    cB
    cW
    @0
    slmdbn0.b
    @0
    eqid
    mndidcl
    cB
    @0
    ne0i
    3syl
end
