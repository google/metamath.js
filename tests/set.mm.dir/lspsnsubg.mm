include "clmod.mm"
include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "clss.mm"
include "csubg.mm"
include "eqid.mm"
include "lspsncl.mm"
include "lsssubg.mm"
include "syldan.mm"

theorem lspsnsubg
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume lspsnsubg.v: |- V = ( Base ` W )
  assume lspsnsubg.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ X e. V ) -> ( N ` { X } ) e. ( SubGrp ` W ) )

  proof
    cW
    clmod
    wcel
    cX
    cV
    wcel
    cX
    csn
    cN
    cfv
    #
    cW
    clss
    cfv
    #
    wcel
    @0
    cW
    csubg
    cfv
    wcel
    @1
    cN
    cV
    cW
    cX
    lspsnsubg.v
    @1
    eqid
    #
    lspsnsubg.n
    lspsncl
    @1
    @0
    cW
    @2
    lsssubg
    syldan
end
