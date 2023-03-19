include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "eqid.mm"
include "islss3.mm"
include "simplbda.mm"

theorem lsslmod
  let cS: class S
  let cU: class U
  let cW: class W
  let cX: class X
  assume lsslss.x: |- X = ( W |`s U )
  assume lsslss.s: |- S = ( LSubSp ` W )


  assert |- ( ( W e. LMod /\ U e. S ) -> X e. LMod )

  proof
    cW
    clmod
    wcel
    cU
    cS
    wcel
    cU
    cW
    cbs
    cfv
    #
    wss
    cX
    clmod
    wcel
    cS
    cU
    @0
    cW
    cX
    lsslss.x
    @0
    eqid
    lsslss.s
    islss3
    simplbda
end
