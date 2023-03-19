include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "w3a.mm"
include "cword.mm"
include "crab.mm"
include "cmpt.mm"
include "cvv.mm"
include "wf1o.mm"
include "wex.mm"
include "wrdexg.mm"
include "adantr.mm"
include "rabexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "3anbi123d.mm"
include "cbvrabv.mm"
include "preq2.mm"
include "mpteq1.mm"
include "ax-mp.mm"
include "wwlktovf1o.mm"
include "adantl.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "sylc.mm"

theorem wrd2f1tovbij
  let vw: setvar w
  let cP: class P
  let vf: setvar f
  let vn: setvar n
  let cV: class V
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x

  disjoint P f
  disjoint P n
  disjoint P w
  disjoint f n
  disjoint f w
  disjoint n w
  disjoint V f
  disjoint V n
  disjoint V w
  disjoint X f
  disjoint X n
  disjoint X w
  disjoint P p
  disjoint P t
  disjoint P u
  disjoint P x
  disjoint f p
  disjoint f t
  disjoint f u
  disjoint f x
  disjoint n p
  disjoint n t
  disjoint n u
  disjoint n x
  disjoint p t
  disjoint p u
  disjoint p w
  disjoint p x
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint u w
  disjoint u x
  disjoint w x
  disjoint V p
  disjoint V t
  disjoint V u
  disjoint V x
  disjoint X p
  disjoint X t
  disjoint X u
  disjoint X x
  assert |- ( ( V e. Y /\ P e. V ) -> E. f f : { w e. Word V | ( ( # ` w ) = 2 /\ ( w ` 0 ) = P /\ { ( w ` 0 ) , ( w ` 1 ) } e. X ) } -1-1-onto-> { n e. V | { P , n } e. X } )

  proof
    cV
    cY
    wcel
    #
    cP
    cV
    wcel
    #
    wa
    #
    vx
    vt
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    cc0
    @3
    cfv
    #
    cP
    wceq
    #
    @6
    c1
    @3
    cfv
    #
    cpr
    #
    cX
    wcel
    #
    w3a
    #
    vt
    cV
    cword
    #
    crab
    #
    c1
    vx
    cv
    cfv
    #
    cmpt
    #
    cvv
    wcel
    #
    vw
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    cc0
    @17
    cfv
    #
    cP
    wceq
    #
    @20
    c1
    @17
    cfv
    #
    cpr
    #
    cX
    wcel
    #
    w3a
    #
    vw
    @12
    crab
    #
    cP
    vn
    cv
    #
    cpr
    #
    cX
    wcel
    #
    vn
    cV
    crab
    #
    @15
    wf1o
    #
    @26
    @30
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @2
    @12
    cvv
    wcel
    #
    @13
    cvv
    wcel
    @16
    @0
    @34
    @1
    cV
    cY
    wrdexg
    adantr
    @11
    vt
    @12
    cvv
    rabexg
    vx
    @13
    @14
    cvv
    mptexg
    3syl
    @1
    @31
    @0
    vu
    vx
    @26
    cP
    @30
    vp
    @15
    cV
    cX
    @25
    vu
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    cc0
    @35
    cfv
    #
    cP
    wceq
    #
    @38
    c1
    @35
    cfv
    #
    cpr
    #
    cX
    wcel
    #
    w3a
    vw
    vu
    @12
    vw
    vu
    weq
    #
    @19
    @37
    @21
    @39
    @24
    @42
    @43
    @18
    @36
    c2
    @17
    @35
    chash
    fveq2
    eqeq1d
    @43
    @20
    @38
    cP
    cc0
    @17
    @35
    fveq1
    #
    eqeq1d
    @43
    @23
    @41
    cX
    @43
    @20
    @38
    @22
    @40
    @44
    c1
    @17
    @35
    fveq1
    preq12d
    eleq1d
    3anbi123d
    cbvrabv
    @29
    cP
    vp
    cv
    #
    cpr
    #
    cX
    wcel
    vn
    vp
    cV
    vn
    vp
    weq
    @28
    @46
    cX
    @27
    @45
    cP
    preq2
    eleq1d
    cbvrabv
    @13
    @26
    wceq
    @15
    vx
    @26
    @14
    cmpt
    wceq
    @11
    @25
    vt
    vw
    @12
    vt
    vw
    weq
    #
    @5
    @19
    @7
    @21
    @10
    @24
    @47
    @4
    @18
    c2
    @3
    @17
    chash
    fveq2
    eqeq1d
    @47
    @6
    @20
    cP
    cc0
    @3
    @17
    fveq1
    #
    eqeq1d
    @47
    @9
    @23
    cX
    @47
    @6
    @20
    @8
    @22
    @48
    c1
    @3
    @17
    fveq1
    preq12d
    eleq1d
    3anbi123d
    cbvrabv
    vx
    @13
    @26
    @14
    mpteq1
    ax-mp
    wwlktovf1o
    adantl
    @33
    @31
    vf
    @15
    cvv
    @26
    @30
    @32
    @15
    f1oeq1
    spcegv
    sylc
end
