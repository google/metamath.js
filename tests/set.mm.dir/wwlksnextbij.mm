include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "cop.mm"
include "csubstr.mm"
include "wceq.mm"
include "clsw.mm"
include "cfv.mm"
include "cpr.mm"
include "wa.mm"
include "crab.mm"
include "wf1o.mm"
include "cmpt.mm"
include "cvv.mm"
include "ovexd.mm"
include "rabexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "chash.mm"
include "c2.mm"
include "w3a.mm"
include "cword.mm"
include "eqid.mm"
include "preq2.mm"
include "eleq1d.mm"
include "cbvrabv.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "preq2d.mm"
include "3anbi123d.mm"
include "mpteq1i.mm"
include "wwlksnextbij0.mm"
include "wwlksnextwrd.mm"
include "eqcomd.mm"
include "mpteq1d.mm"
include "eqidd.mm"
include "f1oeq123d.mm"
include "mpbird.mm"
include "f1oeq1.mm"
include "elabd.mm"

theorem wwlksnextbij
  let vw: setvar w
  let vf: setvar f
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vt: setvar t
  let vx: setvar x
  assume wwlksnextbij.v: |- V = ( Vtx ` G )
  assume wwlksnextbij.e: |- E = ( Edg ` G )

  disjoint E f
  disjoint E n
  disjoint E w
  disjoint f n
  disjoint f w
  disjoint n w
  disjoint G f
  disjoint G w
  disjoint N f
  disjoint N w
  disjoint V f
  disjoint V n
  disjoint V w
  disjoint W f
  disjoint W n
  disjoint W w
  disjoint E p
  disjoint E t
  disjoint E x
  disjoint f p
  disjoint f t
  disjoint f x
  disjoint n p
  disjoint n t
  disjoint n x
  disjoint p t
  disjoint p w
  disjoint p x
  disjoint t w
  disjoint t x
  disjoint w x
  disjoint G t
  disjoint G x
  disjoint N p
  disjoint N t
  disjoint N x
  disjoint V p
  disjoint V t
  disjoint V x
  disjoint W p
  disjoint W t
  disjoint W x
  assert |- ( W e. ( N WWalksN G ) -> E. f f : { w e. ( ( N + 1 ) WWalksN G ) | ( ( w substr <. 0 , ( N + 1 ) >. ) = W /\ { ( lastS ` W ) , ( lastS ` w ) } e. E ) } -1-1-onto-> { n e. V | { ( lastS ` W ) , n } e. E } )

  proof
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    vw
    cv
    #
    cc0
    cN
    c1
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    cW
    wceq
    #
    cW
    clsw
    cfv
    #
    @1
    clsw
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    wa
    vw
    @2
    cG
    cwwlksn
    co
    #
    crab
    #
    @6
    vn
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vn
    cV
    crab
    #
    vf
    cv
    #
    wf1o
    @11
    @15
    vx
    vt
    cv
    #
    @3
    csubstr
    co
    #
    cW
    wceq
    #
    @6
    @17
    clsw
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    wa
    #
    vt
    @10
    crab
    #
    vx
    cv
    clsw
    cfv
    #
    cmpt
    #
    wf1o
    #
    vf
    @26
    @0
    @10
    cvv
    wcel
    @24
    cvv
    wcel
    @26
    cvv
    wcel
    @0
    @2
    cG
    cwwlksn
    ovexd
    @23
    vt
    @10
    cvv
    rabexg
    vx
    @24
    @25
    cvv
    mptexg
    3syl
    @0
    @27
    @1
    chash
    cfv
    #
    cN
    c2
    caddc
    co
    #
    wceq
    #
    @5
    @9
    w3a
    #
    vw
    cV
    cword
    #
    crab
    #
    @15
    vx
    @17
    chash
    cfv
    #
    @29
    wceq
    #
    @19
    @22
    w3a
    #
    vt
    @32
    crab
    #
    @25
    cmpt
    #
    wf1o
    vw
    vx
    @33
    @15
    vp
    cE
    @38
    cG
    cN
    cV
    cW
    wwlksnextbij.v
    wwlksnextbij.e
    @33
    eqid
    #
    @14
    @6
    vp
    cv
    #
    cpr
    #
    cE
    wcel
    vn
    vp
    cV
    @12
    @40
    wceq
    @13
    @41
    cE
    @12
    @40
    @6
    preq2
    eleq1d
    cbvrabv
    vx
    @37
    @33
    @25
    @36
    @31
    vt
    vw
    @32
    @17
    @1
    wceq
    #
    @35
    @30
    @19
    @5
    @22
    @9
    @42
    @34
    @28
    @29
    @17
    @1
    chash
    fveq2
    eqeq1d
    @42
    @18
    @4
    cW
    @17
    @1
    @3
    csubstr
    oveq1
    eqeq1d
    @42
    @21
    @8
    cE
    @42
    @20
    @7
    @6
    @17
    @1
    clsw
    fveq2
    preq2d
    eleq1d
    3anbi123d
    cbvrabv
    mpteq1i
    wwlksnextbij0
    @0
    @11
    @33
    @15
    @15
    @26
    @38
    @0
    vx
    @24
    @37
    @25
    @0
    @37
    @24
    vt
    @37
    cE
    cG
    cN
    cV
    cW
    wwlksnextbij.v
    wwlksnextbij.e
    @37
    eqid
    wwlksnextwrd
    eqcomd
    mpteq1d
    @0
    @33
    @11
    vw
    @33
    cE
    cG
    cN
    cV
    cW
    wwlksnextbij.v
    wwlksnextbij.e
    @39
    wwlksnextwrd
    eqcomd
    @0
    @15
    eqidd
    f1oeq123d
    mpbird
    @11
    @15
    @16
    @26
    f1oeq1
    elabd
end
