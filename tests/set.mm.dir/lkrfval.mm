include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "clk.mm"
include "cfv.mm"
include "clfn.mm"
include "csca.mm"
include "c0g.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "mpteq12dv.mm"
include "df-lkr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem lkrfval
  let cD: class D
  let vf: setvar f
  let cF: class F
  let cK: class K
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  assume lkrfval.d: |- D = ( Scalar ` W )
  assume lkrfval.o: |- .0. = ( 0g ` D )
  assume lkrfval.f: |- F = ( LFnl ` W )
  assume lkrfval.k: |- K = ( LKer ` W )

  disjoint F f
  disjoint W f
  disjoint f w
  disjoint F w
  disjoint .0. w
  disjoint W w
  assert |- ( W e. X -> K = ( f e. F |-> ( `' f " { .0. } ) ) )

  proof
    cW
    cX
    wcel
    cW
    cvv
    wcel
    #
    cK
    vf
    cF
    vf
    cv
    ccnv
    #
    c.0
    csn
    #
    cima
    #
    cmpt
    #
    wceq
    cW
    cX
    elex
    @0
    cK
    cW
    clk
    cfv
    @4
    lkrfval.k
    vw
    cW
    vf
    vw
    cv
    #
    clfn
    cfv
    #
    @1
    @5
    csca
    cfv
    #
    c0g
    cfv
    #
    csn
    #
    cima
    #
    cmpt
    @4
    cvv
    clk
    @5
    cW
    wceq
    #
    vf
    @6
    @10
    cF
    @3
    @11
    @6
    cW
    clfn
    cfv
    #
    cF
    @5
    cW
    clfn
    fveq2
    lkrfval.f
    syl6eqr
    @11
    @9
    @2
    @1
    @11
    @8
    c.0
    @11
    @8
    cD
    c0g
    cfv
    c.0
    @11
    @7
    cD
    c0g
    @11
    @7
    cW
    csca
    cfv
    cD
    @5
    cW
    csca
    fveq2
    lkrfval.d
    syl6eqr
    fveq2d
    lkrfval.o
    syl6eqr
    sneqd
    imaeq2d
    mpteq12dv
    vw
    vf
    df-lkr
    vf
    cF
    @3
    cF
    @12
    cvv
    lkrfval.f
    cW
    clfn
    fvex
    eqeltri
    mptex
    fvmpt
    syl5eq
    syl
end
