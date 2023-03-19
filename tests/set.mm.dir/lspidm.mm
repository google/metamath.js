include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "clss.mm"
include "wceq.mm"
include "eqid.mm"
include "lspcl.mm"
include "lspid.mm"
include "syldan.mm"

theorem lspidm
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cT: class T
  let vt: setvar t
  assume lspss.v: |- V = ( Base ` W )
  assume lspss.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ U C_ V ) -> ( N ` ( N ` U ) ) = ( N ` U ) )

  proof
    cW
    clmod
    wcel
    cU
    cV
    wss
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
    cN
    cfv
    @0
    wceq
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
    cN
    cW
    @2
    lspss.n
    lspid
    syldan
end
