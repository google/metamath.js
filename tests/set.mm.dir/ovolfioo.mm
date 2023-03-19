include "cr.mm"
include "wss.mm"
include "cn.mm"
include "cle.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cioo.mm"
include "ccom.mm"
include "cfv.mm"
include "ciun.mm"
include "crn.mm"
include "cuni.mm"
include "c1st.mm"
include "clt.mm"
include "wbr.mm"
include "c2nd.mm"
include "wrex.mm"
include "wral.mm"
include "wb.mm"
include "cpw.mm"
include "wfn.mm"
include "wceq.mm"
include "cxr.mm"
include "ioof.mm"
include "inss2.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "fss.mm"
include "mpan2.mm"
include "fco.mm"
include "sylancr.mm"
include "ffn.mm"
include "fniunfv.mm"
include "3syl.mm"
include "sseq2d.mm"
include "adantl.mm"
include "wcel.mm"
include "dfss3.mm"
include "ssel2.mm"
include "eliun.mm"
include "co.mm"
include "fvco3.mm"
include "cop.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "1st2nd2.mm"
include "syl.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "w3a.mm"
include "ovolfcl.mm"
include "rexr.mm"
include "elioo1.mm"
include "syl2an.mm"
include "3anass.mm"
include "syl6bb.mm"
include "3adant3.mm"
include "bitrd.mm"
include "adantll.mm"
include "ad2antrr.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "rexbidva.mm"
include "syl5bb.mm"
include "sylan.mm"
include "an32s.mm"
include "ralbidva.mm"
include "bitr3d.mm"

theorem ovolfioo
  let vz: setvar z
  let cA: class A
  let vn: setvar n
  let cF: class F
  let vx: setvar x
  let vy: setvar y

  disjoint n z
  disjoint A n
  disjoint A z
  disjoint F n
  disjoint F z
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  assert |- ( ( A C_ RR /\ F : NN --> ( <_ i^i ( RR X. RR ) ) ) -> ( A C_ U. ran ( (,) o. F ) <-> A. z e. A E. n e. NN ( ( 1st ` ( F ` n ) ) < z /\ z < ( 2nd ` ( F ` n ) ) ) ) )

  proof
    cA
    cr
    wss
    #
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cF
    wf
    #
    wa
    #
    cA
    vn
    cn
    vn
    cv
    #
    cioo
    cF
    ccom
    #
    cfv
    #
    ciun
    #
    wss
    #
    cA
    @6
    crn
    cuni
    #
    wss
    #
    @5
    cF
    cfv
    #
    c1st
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @14
    @12
    c2nd
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    #
    vz
    cA
    wral
    #
    @3
    @9
    @11
    wb
    @0
    @3
    @8
    @10
    cA
    @3
    cn
    cr
    cpw
    #
    @6
    wf
    #
    @6
    cn
    wfn
    @8
    @10
    wceq
    @3
    cxr
    cxr
    cxp
    #
    @21
    cioo
    wf
    cn
    @23
    cF
    wf
    #
    @22
    ioof
    @3
    @2
    @23
    wss
    @24
    @2
    @1
    @23
    cle
    @1
    inss2
    #
    rexpssxrxp
    sstri
    cn
    @2
    @23
    cF
    fss
    mpan2
    cn
    @23
    @21
    cioo
    cF
    fco
    sylancr
    cn
    @21
    @6
    ffn
    vn
    cn
    @6
    fniunfv
    3syl
    sseq2d
    adantl
    @9
    @14
    @8
    wcel
    #
    vz
    cA
    wral
    @4
    @20
    vz
    cA
    @8
    dfss3
    @4
    @26
    @19
    vz
    cA
    @0
    @14
    cA
    wcel
    #
    @3
    @26
    @19
    wb
    #
    @0
    @27
    wa
    @14
    cr
    wcel
    #
    @3
    @28
    cA
    cr
    @14
    ssel2
    @26
    @14
    @7
    wcel
    #
    vn
    cn
    wrex
    @29
    @3
    wa
    #
    @19
    vn
    @14
    cn
    @7
    eliun
    @31
    @30
    @18
    vn
    cn
    @31
    @5
    cn
    wcel
    #
    wa
    #
    @30
    @14
    cxr
    wcel
    #
    @18
    wa
    #
    @18
    @3
    @32
    @30
    @35
    wb
    @29
    @3
    @32
    wa
    #
    @30
    @14
    @13
    @16
    cioo
    co
    #
    wcel
    #
    @35
    @36
    @7
    @37
    @14
    @36
    @7
    @12
    cioo
    cfv
    #
    @37
    cn
    @2
    @5
    cioo
    cF
    fvco3
    @36
    @39
    @13
    @16
    cop
    #
    cioo
    cfv
    @37
    @36
    @12
    @40
    cioo
    @36
    @12
    @1
    wcel
    @12
    @40
    wceq
    @36
    @2
    @1
    @12
    @25
    cn
    @2
    @5
    cF
    ffvelrn
    sseldi
    @12
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @13
    @16
    cioo
    df-ov
    syl6eqr
    eqtrd
    eleq2d
    @36
    @13
    cr
    wcel
    #
    @16
    cr
    wcel
    #
    @13
    @16
    cle
    wbr
    #
    w3a
    @38
    @35
    wb
    #
    cF
    @5
    ovolfcl
    @41
    @42
    @44
    @43
    @41
    @42
    wa
    @38
    @34
    @15
    @17
    w3a
    #
    @35
    @41
    @13
    cxr
    wcel
    @16
    cxr
    wcel
    @38
    @45
    wb
    @42
    @13
    rexr
    @16
    rexr
    @13
    @16
    @14
    elioo1
    syl2an
    @34
    @15
    @17
    3anass
    syl6bb
    3adant3
    syl
    bitrd
    adantll
    @33
    @34
    @18
    @29
    @34
    @3
    @32
    @14
    rexr
    ad2antrr
    biantrurd
    bitr4d
    rexbidva
    syl5bb
    sylan
    an32s
    ralbidva
    syl5bb
    bitr3d
end
