include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "ipidsq.mm"
include "fveq2d.mm"
include "nvcl.mm"
include "nvge0.mm"
include "sqrtsqd.mm"
include "eqtr2d.mm"

theorem ipnm
  let cA: class A
  let cP: class P
  let cU: class U
  let cN: class N
  let cX: class X
  assume ipid.1: |- X = ( BaseSet ` U )
  assume ipid.6: |- N = ( normCV ` U )
  assume ipid.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( N ` A ) = ( sqrt ` ( A P A ) ) )

  proof
    cU
    cnv
    wcel
    cA
    cX
    wcel
    wa
    #
    cA
    cA
    cP
    co
    #
    csqrt
    cfv
    cA
    cN
    cfv
    #
    c2
    cexp
    co
    #
    csqrt
    cfv
    @2
    @0
    @1
    @3
    csqrt
    cA
    cP
    cU
    cN
    cX
    ipid.1
    ipid.6
    ipid.7
    ipidsq
    fveq2d
    @0
    @2
    cA
    cU
    cN
    cX
    ipid.1
    ipid.6
    nvcl
    cA
    cU
    cN
    cX
    ipid.1
    ipid.6
    nvge0
    sqrtsqd
    eqtr2d
end
