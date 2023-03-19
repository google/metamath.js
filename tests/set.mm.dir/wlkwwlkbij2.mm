include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "chash.mm"
include "wceq.mm"
include "cc0.mm"
include "c2nd.mm"
include "wa.mm"
include "cwlks.mm"
include "crab.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cuspgr.mm"
include "cn0.mm"
include "w3a.mm"
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
include "fveq1d.mm"
include "anbi12d.mm"
include "cbvrabv.mm"
include "fveq1.mm"
include "mpteq1i.mm"
include "wlkwwlkbij.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "mpsyl.mm"

theorem wlkwwlkbij2
  let vw: setvar w
  let cP: class P
  let vf: setvar f
  let cG: class G
  let cN: class N
  let cV: class V
  let vp: setvar p
  let vs: setvar s
  let vu: setvar u
  let vx: setvar x
  let vt: setvar t

  disjoint G p
  disjoint G w
  disjoint G f
  disjoint f p
  disjoint N p
  disjoint N w
  disjoint N f
  disjoint P p
  disjoint P w
  disjoint P f
  disjoint f w
  disjoint G s
  disjoint G u
  disjoint p s
  disjoint p u
  disjoint s u
  disjoint G x
  disjoint s w
  disjoint s x
  disjoint u w
  disjoint u x
  disjoint w x
  disjoint G t
  disjoint f t
  disjoint f x
  disjoint p t
  disjoint p x
  disjoint t x
  disjoint N u
  disjoint N s
  disjoint N t
  disjoint N x
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint s t
  disjoint t u
  disjoint P x
  disjoint V s
  disjoint V x
  assert |- ( ( G e. USPGraph /\ P e. V /\ N e. NN0 ) -> E. f f : { p e. ( Walks ` G ) | ( ( # ` ( 1st ` p ) ) = N /\ ( ( 2nd ` p ) ` 0 ) = P ) } -1-1-onto-> { w e. ( N WWalksN G ) | ( w ` 0 ) = P } )

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
    cc0
    @0
    c2nd
    cfv
    #
    cfv
    #
    cP
    wceq
    #
    wa
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
    cP
    cV
    wcel
    cN
    cn0
    wcel
    w3a
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
    cc0
    @12
    c2nd
    cfv
    #
    cfv
    #
    cP
    wceq
    #
    wa
    #
    vp
    @8
    crab
    #
    cc0
    vw
    cv
    #
    cfv
    #
    cP
    wceq
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    @11
    wf1o
    #
    @20
    @25
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @7
    vx
    vt
    @8
    @10
    cG
    cwlks
    fvex
    mptrabex
    vs
    vx
    cP
    @20
    @11
    cG
    cN
    cV
    @25
    vu
    @19
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
    #
    cc0
    @29
    c2nd
    cfv
    #
    cfv
    #
    cP
    wceq
    #
    wa
    vp
    vu
    @8
    vp
    vu
    weq
    #
    @15
    @32
    @18
    @35
    @36
    @14
    @31
    cN
    @36
    @13
    @30
    chash
    @12
    @29
    c1st
    fveq2
    fveq2d
    eqeq1d
    @36
    @17
    @34
    cP
    @36
    cc0
    @16
    @33
    @12
    @29
    c2nd
    fveq2
    fveq1d
    eqeq1d
    anbi12d
    cbvrabv
    @23
    cc0
    vs
    cv
    #
    cfv
    #
    cP
    wceq
    vw
    vs
    @24
    vw
    vs
    weq
    @22
    @38
    cP
    cc0
    @21
    @37
    fveq1
    eqeq1d
    cbvrabv
    vx
    @9
    @20
    @10
    @7
    @19
    vt
    vp
    @8
    vt
    vp
    weq
    #
    @3
    @15
    @6
    @18
    @39
    @2
    @14
    cN
    @39
    @1
    @13
    chash
    @0
    @12
    c1st
    fveq2
    fveq2d
    eqeq1d
    @39
    @5
    @17
    cP
    @39
    cc0
    @4
    @16
    @0
    @12
    c2nd
    fveq2
    fveq1d
    eqeq1d
    anbi12d
    cbvrabv
    mpteq1i
    wlkwwlkbij
    @28
    @26
    vf
    @11
    cvv
    @20
    @25
    @27
    @11
    f1oeq1
    spcegv
    mpsyl
end
