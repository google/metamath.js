include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "clss.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "ssintub.mm"
include "eqid.mm"
include "lspval.mm"
include "syl5sseqr.mm"

theorem lspssid
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cT: class T
  let vt: setvar t
  assume lspss.v: |- V = ( Base ` W )
  assume lspss.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ U C_ V ) -> U C_ ( N ` U ) )

  proof
    cW
    clmod
    wcel
    cU
    cV
    wss
    wa
    cU
    vt
    cv
    wss
    vt
    cW
    clss
    cfv
    #
    crab
    cint
    cU
    cU
    cN
    cfv
    vt
    cU
    @0
    ssintub
    vt
    @0
    cU
    cN
    cV
    cW
    lspss.v
    @0
    eqid
    lspss.n
    lspval
    syl5sseqr
end
