include "cusgr.mm"
include "wcel.mm"
include "cn0.mm"
include "cvtx.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "c1st.mm"
include "chash.mm"
include "wceq.mm"
include "cc0.mm"
include "c2nd.mm"
include "wa.mm"
include "cwlks.mm"
include "crab.mm"
include "cwwlksn.mm"
include "co.mm"
include "wf1o.mm"
include "wex.mm"
include "cmpt.mm"
include "cres.mm"
include "cvv.mm"
include "fvex.mm"
include "mptrabex.mm"
include "resex.mm"
include "eqid.mm"
include "cuspgr.mm"
include "usgruspgr.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "cbvmptv.mm"
include "wlknwwlksnbij.mm"
include "sylan.mm"
include "3adant3.mm"
include "wb.mm"
include "fveq1.mm"
include "3ad2ant3.mm"
include "f1oresrab.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "mpsyl.mm"
include "cab.mm"
include "df-rab.mm"
include "anass.mm"
include "bicomi.mm"
include "abbii.mm"
include "elrab.mm"
include "anbi1i.mm"
include "eqtr4i.mm"
include "3eqtri.mm"
include "f1oeq2.mm"
include "mp1i.mm"
include "exbidv.mm"
include "mpbird.mm"

theorem wlksnwwlknvbij
  let vw: setvar w
  let vf: setvar f
  let cG: class G
  let cN: class N
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t

  disjoint G f
  disjoint G p
  disjoint G w
  disjoint f p
  disjoint f w
  disjoint p w
  disjoint N f
  disjoint N p
  disjoint N w
  disjoint X f
  disjoint X p
  disjoint X w
  disjoint G q
  disjoint f q
  disjoint p q
  disjoint q w
  disjoint G s
  disjoint G t
  disjoint p s
  disjoint p t
  disjoint q s
  disjoint q t
  disjoint s t
  disjoint N q
  disjoint N s
  disjoint N t
  assert |- ( ( G e. USGraph /\ N e. NN0 /\ X e. ( Vtx ` G ) ) -> E. f f : { p e. ( Walks ` G ) | ( ( # ` ( 1st ` p ) ) = N /\ ( ( 2nd ` p ) ` 0 ) = X ) } -1-1-onto-> { w e. ( N WWalksN G ) | ( w ` 0 ) = X } )

  proof
    cG
    cusgr
    wcel
    #
    cN
    cn0
    wcel
    #
    cX
    cG
    cvtx
    cfv
    wcel
    #
    w3a
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
    #
    cc0
    @4
    c2nd
    cfv
    #
    cfv
    #
    cX
    wceq
    #
    wa
    #
    vp
    cG
    cwlks
    cfv
    #
    crab
    #
    cc0
    vw
    cv
    #
    cfv
    #
    cX
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
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @10
    vp
    vq
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
    vq
    @12
    crab
    #
    crab
    #
    @18
    @19
    wf1o
    #
    vf
    wex
    #
    vp
    @25
    @8
    cmpt
    #
    @26
    cres
    #
    cvv
    wcel
    @3
    @26
    @18
    @30
    wf1o
    #
    @28
    @29
    @26
    @24
    vp
    vq
    @12
    @8
    cG
    cwlks
    fvex
    mptrabex
    resex
    @3
    @10
    @16
    vp
    vw
    @25
    @17
    @8
    @29
    @29
    eqid
    @0
    @1
    @25
    @17
    @29
    wf1o
    #
    @2
    @0
    cG
    cuspgr
    wcel
    @1
    @32
    cG
    usgruspgr
    vs
    @25
    @29
    cG
    cN
    @17
    vt
    @24
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
    vq
    vt
    @12
    vq
    vt
    weq
    #
    @23
    @35
    cN
    @36
    @22
    @34
    chash
    @21
    @33
    c1st
    fveq2
    fveq2d
    eqeq1d
    cbvrabv
    @17
    eqid
    vp
    vs
    @25
    @8
    vs
    cv
    #
    c2nd
    cfv
    @4
    @37
    c2nd
    fveq2
    cbvmptv
    wlknwwlksnbij
    sylan
    3adant3
    @14
    @8
    wceq
    #
    @3
    @16
    @10
    wb
    @4
    @25
    wcel
    #
    @38
    @15
    @9
    cX
    cc0
    @14
    @8
    fveq1
    eqeq1d
    3ad2ant3
    f1oresrab
    @27
    @31
    vf
    @30
    cvv
    @26
    @18
    @19
    @30
    f1oeq1
    spcegv
    mpsyl
    @3
    @20
    @27
    vf
    @13
    @26
    wceq
    @20
    @27
    wb
    @3
    @13
    @4
    @12
    wcel
    #
    @11
    wa
    #
    vp
    cab
    @40
    @7
    wa
    #
    @10
    wa
    #
    vp
    cab
    #
    @26
    @11
    vp
    @12
    df-rab
    @41
    @43
    vp
    @43
    @41
    @40
    @7
    @10
    anass
    bicomi
    abbii
    @44
    @39
    @10
    wa
    #
    vp
    cab
    @26
    @43
    @45
    vp
    @45
    @43
    @39
    @42
    @10
    @24
    @7
    vq
    @4
    @12
    vq
    vp
    weq
    #
    @23
    @6
    cN
    @46
    @22
    @5
    chash
    @21
    @4
    c1st
    fveq2
    fveq2d
    eqeq1d
    elrab
    anbi1i
    bicomi
    abbii
    @10
    vp
    @25
    df-rab
    eqtr4i
    3eqtri
    @13
    @26
    @18
    @19
    f1oeq2
    mp1i
    exbidv
    mpbird
end
