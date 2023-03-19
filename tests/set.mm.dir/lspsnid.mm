include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "snssi.mm"
include "lspssid.mm"
include "sylan2.mm"
include "wb.mm"
include "snssg.mm"
include "adantl.mm"
include "mpbird.mm"

theorem lspsnid
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume lspsnid.v: |- V = ( Base ` W )
  assume lspsnid.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ X e. V ) -> X e. ( N ` { X } ) )

  proof
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    cX
    cX
    csn
    #
    cN
    cfv
    #
    wcel
    #
    @2
    @3
    wss
    #
    @1
    @0
    @2
    cV
    wss
    @5
    cX
    cV
    snssi
    @2
    cN
    cV
    cW
    lspsnid.v
    lspsnid.n
    lspssid
    sylan2
    @1
    @4
    @5
    wb
    @0
    cX
    @3
    cV
    snssg
    adantl
    mpbird
end
