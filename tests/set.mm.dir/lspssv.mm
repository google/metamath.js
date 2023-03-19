include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "clss.mm"
include "eqid.mm"
include "lspcl.mm"
include "lssss.mm"
include "syl.mm"

theorem lspssv
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cT: class T
  let vt: setvar t
  assume lspss.v: |- V = ( Base ` W )
  assume lspss.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ U C_ V ) -> ( N ` U ) C_ V )

  proof
    cW
    clmod
    wcel
    cU
    cV
    wss
    wa
    cU
    cN
    cfv
    #
    cW
    clss
    cfv
    #
    wcel
    @0
    cV
    wss
    @1
    cU
    cN
    cV
    cW
    lspss.v
    @1
    eqid
    #
    lspss.n
    lspcl
    @1
    @0
    cV
    cW
    lspss.v
    @2
    lssss
    syl
end
