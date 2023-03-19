include "cuspgr.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "wlknwwlksnfun.mm"
include "sylan.mm"
include "c2nd.mm"
include "wb.mm"
include "fveq2.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eqeqan12d.mm"
include "adantl.mm"
include "cwlks.mm"
include "c1st.mm"
include "chash.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "anbi12i.mm"
include "uspgr2wlkeq2.mm"
include "3expb.mm"
include "sylan2b.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem wlknwwlksninj
  let vt: setvar t
  let cT: class T
  let cF: class F
  let cG: class G
  let cN: class N
  let cW: class W
  let vp: setvar p
  let vv: setvar v
  let vw: setvar w
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
  disjoint F v
  disjoint F w
  disjoint v w
  disjoint G v
  disjoint G w
  disjoint p v
  disjoint p w
  disjoint t v
  disjoint t w
  disjoint N v
  disjoint N w
  disjoint T v
  disjoint T w
  assert |- ( ( G e. USPGraph /\ N e. NN0 ) -> F : T -1-1-> W )

  proof
    cG
    cuspgr
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cT
    cW
    cF
    wf
    #
    vv
    cv
    #
    cF
    cfv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vv
    vw
    weq
    #
    wi
    #
    vw
    cT
    wral
    vv
    cT
    wral
    cT
    cW
    cF
    wf1
    @0
    cG
    cupgr
    wcel
    @1
    @3
    cG
    uspgrupgr
    vt
    cT
    cF
    cG
    cN
    cW
    vp
    wlknwwlksnbij.t
    wlknwwlksnbij.w
    wlknwwlksnbij.f
    wlknwwlksnfun
    sylan
    @2
    @10
    vv
    vw
    cT
    cT
    @2
    @4
    cT
    wcel
    #
    @6
    cT
    wcel
    #
    wa
    #
    wa
    @8
    @4
    c2nd
    cfv
    #
    @6
    c2nd
    cfv
    #
    wceq
    #
    @9
    @13
    @8
    @16
    wb
    @2
    @11
    @12
    @5
    @14
    @7
    @15
    vt
    @4
    vt
    cv
    #
    c2nd
    cfv
    #
    @14
    cT
    cF
    @17
    @4
    c2nd
    fveq2
    wlknwwlksnbij.f
    @4
    c2nd
    fvex
    fvmpt
    vt
    @6
    @18
    @15
    cT
    cF
    @17
    @6
    c2nd
    fveq2
    wlknwwlksnbij.f
    @6
    c2nd
    fvex
    fvmpt
    eqeqan12d
    adantl
    @13
    @2
    @4
    cG
    cwlks
    cfv
    #
    wcel
    @4
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
    #
    @6
    @19
    wcel
    @6
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
    #
    wa
    @16
    @9
    wi
    #
    @11
    @23
    @12
    @27
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
    @22
    vp
    @4
    @19
    cT
    vp
    vv
    weq
    #
    @31
    @21
    cN
    @33
    @30
    @20
    chash
    @29
    @4
    c1st
    fveq2
    fveq2d
    eqeq1d
    wlknwwlksnbij.t
    elrab2
    @32
    @26
    vp
    @6
    @19
    cT
    vp
    vw
    weq
    #
    @31
    @25
    cN
    @34
    @30
    @24
    chash
    @29
    @6
    c1st
    fveq2
    fveq2d
    eqeq1d
    wlknwwlksnbij.t
    elrab2
    anbi12i
    @2
    @23
    @27
    @28
    @4
    @6
    cG
    cN
    uspgr2wlkeq2
    3expb
    sylan2b
    sylbid
    ralrimivva
    vv
    vw
    cT
    cW
    cF
    dff13
    sylanbrc
end
