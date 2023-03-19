include "cupgr.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "cwwlksn.mm"
include "co.mm"
include "cwlks.mm"
include "c1st.mm"
include "chash.mm"
include "wceq.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "wlknewwlksn.mm"
include "an4s.mm"
include "sylan2b.mm"
include "syl6eleqr.mm"
include "fmptd.mm"

theorem wlknwwlksnfun
  let vt: setvar t
  let cT: class T
  let cF: class F
  let cG: class G
  let cN: class N
  let cW: class W
  let vp: setvar p
  assume wlknwwlksnbij.t: |- T = { p e. ( Walks ` G ) | ( # ` ( 1st ` p ) ) = N }
  assume wlknwwlksnbij.w: |- W = ( N WWalksN G )
  assume wlknwwlksnbij.f: |- F = ( t e. T |-> ( 2nd ` t ) )

  disjoint G p
  disjoint G t
  disjoint p t
  disjoint N p
  disjoint N t
  disjoint T t
  disjoint W t
  assert |- ( ( G e. UPGraph /\ N e. NN0 ) -> F : T --> W )

  proof
    cG
    cupgr
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    vt
    cT
    vt
    cv
    #
    c2nd
    cfv
    #
    cW
    cF
    @2
    @3
    cT
    wcel
    #
    wa
    @4
    cN
    cG
    cwwlksn
    co
    #
    cW
    @5
    @2
    @3
    cG
    cwlks
    cfv
    #
    wcel
    #
    @3
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    @4
    @6
    wcel
    #
    vp
    cv
    #
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    @11
    vp
    @3
    @7
    cT
    vp
    vt
    weq
    #
    @15
    @10
    cN
    @16
    @14
    @9
    chash
    @13
    @3
    c1st
    fveq2
    fveq2d
    eqeq1d
    wlknwwlksnbij.t
    elrab2
    @0
    @8
    @1
    @11
    @12
    cG
    cN
    @3
    wlknewwlksn
    an4s
    sylan2b
    wlknwwlksnbij.w
    syl6eleqr
    wlknwwlksnbij.f
    fmptd
end
