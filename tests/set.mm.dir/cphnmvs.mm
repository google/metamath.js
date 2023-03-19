include "ccph.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cnm.mm"
include "cmul.mm"
include "cabs.mm"
include "cnlm.mm"
include "wceq.mm"
include "cphnlm.mm"
include "eqid.mm"
include "nmvs.mm"
include "syl3an1.mm"
include "cclm.mm"
include "cphclm.mm"
include "clmabs.mm"
include "sylan.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "eqtr4d.mm"

theorem cphnmvs
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume cphnmvs.v: |- V = ( Base ` W )
  assume cphnmvs.n: |- N = ( norm ` W )
  assume cphnmvs.s: |- .x. = ( .s ` W )
  assume cphnmvs.f: |- F = ( Scalar ` W )
  assume cphnmvs.k: |- K = ( Base ` F )


  assert |- ( ( W e. CPreHil /\ X e. K /\ Y e. V ) -> ( N ` ( X .x. Y ) ) = ( ( abs ` X ) x. ( N ` Y ) ) )

  proof
    cW
    ccph
    wcel
    #
    cX
    cK
    wcel
    #
    cY
    cV
    wcel
    #
    w3a
    #
    cX
    cY
    c.x
    co
    cN
    cfv
    #
    cX
    cF
    cnm
    cfv
    #
    cfv
    #
    cY
    cN
    cfv
    #
    cmul
    co
    #
    cX
    cabs
    cfv
    #
    @7
    cmul
    co
    @0
    cW
    cnlm
    wcel
    @1
    @2
    @4
    @8
    wceq
    cW
    cphnlm
    @5
    c.x
    cF
    cK
    cN
    cV
    cW
    cX
    cY
    cphnmvs.v
    cphnmvs.n
    cphnmvs.s
    cphnmvs.f
    cphnmvs.k
    @5
    eqid
    nmvs
    syl3an1
    @3
    @9
    @6
    @7
    cmul
    @0
    @1
    @9
    @6
    wceq
    #
    @2
    @0
    cW
    cclm
    wcel
    @1
    @10
    cW
    cphclm
    cX
    cF
    cK
    cW
    cphnmvs.f
    cphnmvs.k
    clmabs
    sylan
    3adant3
    oveq1d
    eqtr4d
end
