include "c1.mm"
include "cv.mm"
include "cfv.mm"
include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cc0.mm"
include "cpr.mm"
include "w3a.mm"
include "wa.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "wrdf.mm"
include "wi.mm"
include "oveq2.mm"
include "feq2d.mm"
include "cn0.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "1nn0.mm"
include "2nn.mm"
include "1lt2.mm"
include "elfzo0.mm"
include "mpbir3an.mm"
include "ffvelrn.mm"
include "mpan2.mm"
include "syl6bi.mm"
include "3ad2ant1.mm"
include "mpan9.mm"
include "preq1.mm"
include "eleq1d.mm"
include "biimpa.mm"
include "3adant1.mm"
include "adantl.mm"
include "jca.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "preq12d.mm"
include "3anbi123d.mm"
include "elrab2.mm"
include "preq2.mm"
include "3imtr4i.mm"
include "fmpti.mm"

theorem wwlktovf
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cP: class P
  let cR: class R
  let vn: setvar n
  let cF: class F
  let cV: class V
  let cX: class X
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
  assert |- F : D --> R

  proof
    vt
    cD
    cR
    c1
    vt
    cv
    #
    cfv
    #
    cF
    wrd2f1tovbij.f
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
    @6
    @1
    cpr
    #
    cX
    wcel
    #
    w3a
    #
    wa
    #
    @1
    cV
    wcel
    #
    cP
    @1
    cpr
    #
    cX
    wcel
    #
    wa
    @0
    cD
    wcel
    @1
    cR
    wcel
    @11
    @12
    @14
    @3
    cc0
    @4
    cfzo
    co
    #
    cV
    @0
    wf
    #
    @10
    @12
    cV
    @0
    wrdf
    @5
    @7
    @16
    @12
    wi
    @9
    @5
    @16
    cc0
    c2
    cfzo
    co
    #
    cV
    @0
    wf
    #
    @12
    @5
    @15
    @17
    cV
    @0
    @4
    c2
    cc0
    cfzo
    oveq2
    feq2d
    @18
    c1
    @17
    wcel
    #
    @12
    @19
    c1
    cn0
    wcel
    c2
    cn
    wcel
    c1
    c2
    clt
    wbr
    1nn0
    2nn
    1lt2
    c1
    c2
    elfzo0
    mpbir3an
    @17
    cV
    c1
    @0
    ffvelrn
    mpan2
    syl6bi
    3ad2ant1
    mpan9
    @10
    @14
    @3
    @7
    @9
    @14
    @5
    @7
    @9
    @14
    @7
    @8
    @13
    cX
    @6
    cP
    @1
    preq1
    eleq1d
    biimpa
    3adant1
    adantl
    jca
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
    @20
    cfv
    #
    cP
    wceq
    #
    @23
    c1
    @20
    cfv
    #
    cpr
    #
    cX
    wcel
    #
    w3a
    @10
    vw
    @0
    @2
    cD
    vw
    vt
    weq
    #
    @22
    @5
    @24
    @7
    @27
    @9
    @28
    @21
    @4
    c2
    @20
    @0
    chash
    fveq2
    eqeq1d
    @28
    @23
    @6
    cP
    cc0
    @20
    @0
    fveq1
    #
    eqeq1d
    @28
    @26
    @8
    cX
    @28
    @23
    @6
    @25
    @1
    @29
    c1
    @20
    @0
    fveq1
    preq12d
    eleq1d
    3anbi123d
    wrd2f1tovbij.d
    elrab2
    cP
    vn
    cv
    #
    cpr
    #
    cX
    wcel
    @14
    vn
    @1
    cV
    cR
    @30
    @1
    wceq
    @31
    @13
    cX
    @30
    @1
    cP
    preq2
    eleq1d
    wrd2f1tovbij.r
    elrab2
    3imtr4i
    fmpti
end
