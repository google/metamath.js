include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "lssss.mm"
include "lspval.mm"
include "sylan2.mm"
include "intmin.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem lspid
  let cS: class S
  let cU: class U
  let cN: class N
  let cW: class W
  let vt: setvar t
  assume lspid.s: |- S = ( LSubSp ` W )
  assume lspid.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ U e. S ) -> ( N ` U ) = U )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    cU
    cN
    cfv
    #
    cU
    vt
    cv
    wss
    vt
    cS
    crab
    cint
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
    wceq
    cS
    cU
    @4
    cW
    @4
    eqid
    #
    lspid.s
    lssss
    vt
    cS
    cU
    cN
    @4
    cW
    @5
    lspid.s
    lspid.n
    lspval
    sylan2
    @1
    @3
    cU
    wceq
    @0
    vt
    cU
    cS
    intmin
    adantl
    eqtrd
end
