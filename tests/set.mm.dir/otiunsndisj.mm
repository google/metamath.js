include "wcel.mm"
include "weq.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cotp.mm"
include "ciun.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "wdisj.mm"
include "wa.mm"
include "wn.mm"
include "wrex.mm"
include "eliun.mm"
include "wi.mm"
include "w3a.mm"
include "otthg.mm"
include "simp1.mm"
include "syl6bi.mm"
include "con3d.mm"
include "3exp.mm"
include "impcom.mm"
include "com3r.mm"
include "imp31.mm"
include "wb.mm"
include "velsn.mm"
include "eqeq1.mm"
include "notbid.mm"
include "sylbi.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "sylnibr.mm"
include "adantr.mm"
include "nrexdv.mm"
include "ex.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "oteq3.mm"
include "sneqd.mm"
include "cbviunv.mm"
include "eleq2i.mm"
include "notbii.mm"
include "ralbii.mm"
include "sylibr.mm"
include "disj.mm"
include "expcom.mm"
include "orrd.mm"
include "adantrr.mm"
include "ralrimivva.mm"
include "sneq.mm"
include "difeq2d.mm"
include "oteq1.mm"
include "iuneq12d.mm"
include "disjor.mm"

theorem otiunsndisj
  let cB: class B
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vs: setvar s

  disjoint B a
  disjoint B c
  disjoint a c
  disjoint V a
  disjoint V c
  disjoint W a
  disjoint W c
  disjoint X a
  disjoint X c
  disjoint B d
  disjoint B e
  disjoint B s
  disjoint a d
  disjoint a e
  disjoint a s
  disjoint c d
  disjoint c e
  disjoint c s
  disjoint d e
  disjoint d s
  disjoint e s
  disjoint V d
  disjoint V e
  disjoint V s
  disjoint W d
  disjoint W e
  disjoint W s
  disjoint X d
  disjoint X e
  disjoint X s
  assert |- ( B e. X -> Disj_ a e. V U_ c e. ( W \ { a } ) { <. a , B , c >. } )

  proof
    cB
    cX
    wcel
    #
    va
    vd
    weq
    #
    vc
    cW
    va
    cv
    #
    csn
    #
    cdif
    #
    @2
    cB
    vc
    cv
    #
    cotp
    #
    csn
    #
    ciun
    #
    vc
    cW
    vd
    cv
    #
    csn
    #
    cdif
    #
    @9
    cB
    @5
    cotp
    #
    csn
    #
    ciun
    #
    cin
    c0
    wceq
    #
    wo
    #
    vd
    cV
    wral
    va
    cV
    wral
    va
    cV
    @8
    wdisj
    @0
    @16
    va
    vd
    cV
    cV
    @0
    @2
    cV
    wcel
    #
    @16
    @9
    cV
    wcel
    @0
    @17
    wa
    #
    @1
    @15
    @1
    wn
    #
    @18
    @15
    @19
    @18
    wa
    #
    vs
    cv
    #
    @14
    wcel
    #
    wn
    #
    vs
    @8
    wral
    #
    @15
    @20
    @21
    ve
    @11
    @9
    cB
    ve
    cv
    #
    cotp
    #
    csn
    #
    ciun
    #
    wcel
    #
    wn
    #
    vs
    @8
    wral
    @24
    @20
    @30
    vs
    @8
    @21
    @8
    wcel
    @21
    @7
    wcel
    #
    vc
    @4
    wrex
    @20
    @30
    vc
    @21
    @4
    @7
    eliun
    @20
    @31
    @30
    vc
    @4
    @20
    @5
    @4
    wcel
    #
    wa
    #
    @31
    @30
    @33
    @31
    wa
    #
    @21
    @27
    wcel
    #
    ve
    @11
    wrex
    @29
    @34
    @35
    ve
    @11
    @34
    @35
    wn
    @25
    @11
    wcel
    @34
    @21
    @26
    wceq
    #
    @35
    @33
    @31
    @36
    wn
    #
    @33
    @37
    @31
    @6
    @26
    wceq
    #
    wn
    #
    @19
    @18
    @32
    @39
    @18
    @32
    @19
    @39
    @17
    @0
    @32
    @19
    @39
    wi
    #
    wi
    @17
    @0
    @32
    @40
    @17
    @0
    @32
    w3a
    #
    @38
    @1
    @41
    @38
    @1
    cB
    cB
    wceq
    #
    vc
    ve
    weq
    #
    w3a
    @1
    @2
    cB
    @5
    @9
    cV
    cB
    @25
    cX
    @4
    otthg
    @1
    @42
    @43
    simp1
    syl6bi
    con3d
    3exp
    impcom
    com3r
    imp31
    @31
    @21
    @6
    wceq
    #
    @37
    @39
    wb
    vs
    @6
    velsn
    @44
    @36
    @38
    @21
    @6
    @26
    eqeq1
    notbid
    sylbi
    syl5ibrcom
    imp
    vs
    @26
    velsn
    sylnibr
    adantr
    nrexdv
    ve
    @21
    @11
    @27
    eliun
    sylnibr
    ex
    rexlimdva
    syl5bi
    ralrimiv
    @23
    @30
    vs
    @8
    @22
    @29
    @14
    @28
    @21
    vc
    ve
    @11
    @13
    @27
    @43
    @12
    @26
    @5
    @25
    @9
    cB
    oteq3
    sneqd
    cbviunv
    eleq2i
    notbii
    ralbii
    sylibr
    vs
    @8
    @14
    disj
    sylibr
    expcom
    orrd
    adantrr
    ralrimivva
    cV
    @8
    @14
    va
    vd
    @1
    vc
    @4
    @11
    @7
    @13
    @1
    @3
    @10
    cW
    @2
    @9
    sneq
    difeq2d
    @1
    @6
    @12
    @2
    @9
    cB
    @5
    oteq1
    sneqd
    iuneq12d
    disjor
    sylibr
end
