include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "chash.mm"
include "wceq.mm"
include "cwlks.mm"
include "crab.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cuspgr.mm"
include "cn0.mm"
include "wa.mm"
include "cwwlksn.mm"
include "co.mm"
include "wf1o.mm"
include "wex.mm"
include "fvex.mm"
include "mptrabex.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "eqid.mm"
include "mpteq1i.mm"
include "wlknwwlksnbij.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "mpsyl.mm"

theorem wlknwwlksnbij2
  let vf: setvar f
  let cG: class G
  let cN: class N
  let vp: setvar p
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x

  disjoint G f
  disjoint G p
  disjoint f p
  disjoint N f
  disjoint N p
  disjoint G t
  disjoint G u
  disjoint G x
  disjoint f t
  disjoint f u
  disjoint f x
  disjoint p t
  disjoint p u
  disjoint p x
  disjoint t u
  disjoint t x
  disjoint u x
  disjoint N t
  disjoint N u
  disjoint N x
  assert |- ( ( G e. USPGraph /\ N e. NN0 ) -> E. f f : { p e. ( Walks ` G ) | ( # ` ( 1st ` p ) ) = N } -1-1-onto-> ( N WWalksN G ) )

  proof
    vx
    vt
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
    #
    vt
    cG
    cwlks
    cfv
    #
    crab
    #
    vx
    cv
    c2nd
    cfv
    #
    cmpt
    #
    cvv
    wcel
    cG
    cuspgr
    wcel
    cN
    cn0
    wcel
    wa
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
    #
    vp
    @4
    crab
    #
    cN
    cG
    cwwlksn
    co
    #
    @7
    wf1o
    #
    @12
    @13
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @3
    vx
    vt
    @4
    @6
    cG
    cwlks
    fvex
    mptrabex
    vx
    @12
    @7
    cG
    cN
    @13
    vu
    @11
    vu
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
    vp
    vu
    @4
    vp
    vu
    weq
    #
    @10
    @19
    cN
    @20
    @9
    @18
    chash
    @8
    @17
    c1st
    fveq2
    fveq2d
    eqeq1d
    cbvrabv
    @13
    eqid
    vx
    @5
    @12
    @6
    @3
    @11
    vt
    vp
    @4
    vt
    vp
    weq
    #
    @2
    @10
    cN
    @21
    @1
    @9
    chash
    @0
    @8
    c1st
    fveq2
    fveq2d
    eqeq1d
    cbvrabv
    mpteq1i
    wlknwwlksnbij
    @16
    @14
    vf
    @7
    cvv
    @12
    @13
    @15
    @7
    f1oeq1
    spcegv
    mpsyl
end
