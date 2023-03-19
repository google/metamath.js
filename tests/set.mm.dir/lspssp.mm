include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "lssss.mm"
include "lspss.mm"
include "syl3an2.mm"
include "wceq.mm"
include "lspid.mm"
include "3adant3.mm"
include "sseqtrd.mm"

theorem lspssp
  let cS: class S
  let cT: class T
  let cU: class U
  let cN: class N
  let cW: class W
  assume lspssp.s: |- S = ( LSubSp ` W )
  assume lspssp.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ U e. S /\ T C_ U ) -> ( N ` T ) C_ U )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    cT
    cU
    wss
    #
    w3a
    cT
    cN
    cfv
    #
    cU
    cN
    cfv
    #
    cU
    @1
    @0
    cU
    cW
    cbs
    cfv
    #
    wss
    @2
    @3
    @4
    wss
    cS
    cU
    @5
    cW
    @5
    eqid
    #
    lspssp.s
    lssss
    cT
    cU
    cN
    @5
    cW
    @6
    lspssp.n
    lspss
    syl3an2
    @0
    @1
    @4
    cU
    wceq
    @2
    cS
    cU
    cN
    cW
    lspssp.s
    lspssp.n
    lspid
    3adant3
    sseqtrd
end
