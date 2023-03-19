include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wwlktovf.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "fveq1.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eqeqan12d.mm"
include "cword.mm"
include "chash.mm"
include "c2.mm"
include "cc0.mm"
include "cpr.mm"
include "w3a.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "3anbi123d.mm"
include "elrab2.mm"
include "cfzo.mm"
include "co.mm"
include "simp1.mm"
include "adantl.mm"
include "eqcomd.mm"
include "sylan9eq.mm"
include "adantr.mm"
include "simp2.mm"
include "simpr.mm"
include "wb.mm"
include "oveq2.mm"
include "fzo0to2pr.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "c0ex.mm"
include "1ex.mm"
include "eqeq12d.mm"
include "ralpr.mm"
include "syl6bb.mm"
include "3ad2ant1.mm"
include "ad3antlr.mm"
include "mpbir2and.mm"
include "simpl.mm"
include "anim12i.mm"
include "eqwrd.mm"
include "syl.mm"
include "ex.mm"
include "syl2anb.mm"
include "sylbid.mm"
include "rgen2a.mm"
include "dff13.mm"
include "mpbir2an.mm"

theorem wwlktovf1
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cP: class P
  let cR: class R
  let vn: setvar n
  let cF: class F
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  assume wrd2f1tovbij.d: |- D = { w e. Word V | ( ( # ` w ) = 2 /\ ( w ` 0 ) = P /\ { ( w ` 0 ) , ( w ` 1 ) } e. X ) }
  assume wrd2f1tovbij.r: |- R = { n e. V | { P , n } e. X }
  assume wrd2f1tovbij.f: |- F = ( t e. D |-> ( t ` 1 ) )

  disjoint D t
  disjoint P n
  disjoint P t
  disjoint P w
  disjoint n t
  disjoint n w
  disjoint t w
  disjoint R t
  disjoint V n
  disjoint V t
  disjoint V w
  disjoint X n
  disjoint X w
  disjoint D x
  disjoint D y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint P x
  disjoint P y
  disjoint t x
  disjoint t y
  disjoint w x
  disjoint w y
  disjoint V x
  disjoint V y
  disjoint i x
  disjoint i y
  assert |- F : D -1-1-> R

  proof
    cD
    cR
    cF
    wf1
    cD
    cR
    cF
    wf
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cD
    wral
    vx
    cD
    wral
    vw
    vt
    cD
    cP
    cR
    vn
    cF
    cV
    cX
    wrd2f1tovbij.d
    wrd2f1tovbij.r
    wrd2f1tovbij.f
    wwlktovf
    @6
    vx
    vy
    cD
    @0
    cD
    wcel
    #
    @2
    cD
    wcel
    #
    wa
    @4
    c1
    @0
    cfv
    #
    c1
    @2
    cfv
    #
    wceq
    #
    @5
    @7
    @8
    @1
    @9
    @3
    @10
    vt
    @0
    c1
    vt
    cv
    #
    cfv
    #
    @9
    cD
    cF
    c1
    @12
    @0
    fveq1
    wrd2f1tovbij.f
    c1
    @0
    fvex
    fvmpt
    vt
    @2
    @13
    @10
    cD
    cF
    c1
    @12
    @2
    fveq1
    wrd2f1tovbij.f
    c1
    @2
    fvex
    fvmpt
    eqeqan12d
    @7
    @0
    cV
    cword
    #
    wcel
    #
    @0
    chash
    cfv
    #
    c2
    wceq
    #
    cc0
    @0
    cfv
    #
    cP
    wceq
    #
    @18
    @9
    cpr
    #
    cX
    wcel
    #
    w3a
    #
    wa
    #
    @2
    @14
    wcel
    #
    @2
    chash
    cfv
    #
    c2
    wceq
    #
    cc0
    @2
    cfv
    #
    cP
    wceq
    #
    @27
    @10
    cpr
    #
    cX
    wcel
    #
    w3a
    #
    wa
    #
    @11
    @5
    wi
    @8
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
    @33
    cfv
    #
    cP
    wceq
    #
    @36
    c1
    @33
    cfv
    #
    cpr
    #
    cX
    wcel
    #
    w3a
    #
    @22
    vw
    @0
    @14
    cD
    vw
    vx
    weq
    #
    @35
    @17
    @37
    @19
    @40
    @21
    @42
    @34
    @16
    c2
    @33
    @0
    chash
    fveq2
    eqeq1d
    @42
    @36
    @18
    cP
    cc0
    @33
    @0
    fveq1
    #
    eqeq1d
    @42
    @39
    @20
    cX
    @42
    @36
    @18
    @38
    @9
    @43
    c1
    @33
    @0
    fveq1
    preq12d
    eleq1d
    3anbi123d
    wrd2f1tovbij.d
    elrab2
    @41
    @31
    vw
    @2
    @14
    cD
    vw
    vy
    weq
    #
    @35
    @26
    @37
    @28
    @40
    @30
    @44
    @34
    @25
    c2
    @33
    @2
    chash
    fveq2
    eqeq1d
    @44
    @36
    @27
    cP
    cc0
    @33
    @2
    fveq1
    #
    eqeq1d
    @44
    @39
    @29
    cX
    @44
    @36
    @27
    @38
    @10
    @45
    c1
    @33
    @2
    fveq1
    preq12d
    eleq1d
    3anbi123d
    wrd2f1tovbij.d
    elrab2
    @23
    @32
    wa
    #
    @11
    @5
    @46
    @11
    wa
    #
    @5
    @16
    @25
    wceq
    #
    vi
    cv
    #
    @0
    cfv
    #
    @49
    @2
    cfv
    #
    wceq
    #
    vi
    cc0
    @16
    cfzo
    co
    #
    wral
    #
    @46
    @48
    @11
    @23
    @32
    @16
    c2
    @25
    @22
    @17
    @15
    @17
    @19
    @21
    simp1
    adantl
    @31
    c2
    @25
    wceq
    @24
    @31
    @25
    c2
    @26
    @28
    @30
    simp1
    eqcomd
    adantl
    sylan9eq
    adantr
    @47
    @54
    @18
    @27
    wceq
    #
    @11
    @46
    @55
    @11
    @23
    @32
    @18
    cP
    @27
    @22
    @19
    @15
    @17
    @19
    @21
    simp2
    adantl
    @31
    cP
    @27
    wceq
    @24
    @31
    @27
    cP
    @26
    @28
    @30
    simp2
    eqcomd
    adantl
    sylan9eq
    adantr
    @46
    @11
    simpr
    @22
    @54
    @55
    @11
    wa
    #
    wb
    #
    @15
    @32
    @11
    @17
    @19
    @57
    @21
    @17
    @54
    @52
    vi
    cc0
    c1
    cpr
    #
    wral
    @56
    @17
    @52
    vi
    @53
    @58
    @17
    @53
    cc0
    c2
    cfzo
    co
    @58
    @16
    c2
    cc0
    cfzo
    oveq2
    fzo0to2pr
    syl6eq
    raleqdv
    @52
    @55
    @11
    vi
    cc0
    c1
    c0ex
    1ex
    @49
    cc0
    wceq
    @50
    @18
    @51
    @27
    @49
    cc0
    @0
    fveq2
    @49
    cc0
    @2
    fveq2
    eqeq12d
    @49
    c1
    wceq
    @50
    @9
    @51
    @10
    @49
    c1
    @0
    fveq2
    @49
    c1
    @2
    fveq2
    eqeq12d
    ralpr
    syl6bb
    3ad2ant1
    ad3antlr
    mpbir2and
    @47
    @15
    @24
    wa
    #
    @5
    @48
    @54
    wa
    wb
    @46
    @59
    @11
    @23
    @15
    @32
    @24
    @15
    @22
    simpl
    @24
    @31
    simpl
    anim12i
    adantr
    @0
    vi
    cV
    @2
    eqwrd
    syl
    mpbir2and
    ex
    syl2anb
    sylbid
    rgen2a
    vx
    vy
    cD
    cR
    cF
    dff13
    mpbir2an
end
