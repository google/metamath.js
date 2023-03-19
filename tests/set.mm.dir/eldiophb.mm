include "cdioph.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cmap.mm"
include "wrex.mm"
include "cab.mm"
include "cmzp.mm"
include "cuz.mm"
include "cdm.mm"
include "cmpt2.mm"
include "crn.mm"
include "df-dioph.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "fveq2.mm"
include "eqidd.mm"
include "oveq2.mm"
include "reseq2d.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "mpt2eq123dv.mm"
include "rneqd.mm"
include "cpw.mm"
include "ovex.mm"
include "pwex.mm"
include "eqid.mm"
include "rnmpt2.mm"
include "wss.mm"
include "wf.mm"
include "elmapi.mm"
include "fzss2.mm"
include "fssres.mm"
include "syl2anr.mm"
include "nn0ex.mm"
include "elmap.mm"
include "sylibr.mm"
include "wb.mm"
include "eleq1.mm"
include "adantr.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "abssdv.mm"
include "elpw2.mm"
include "rexlimdvw.mm"
include "rexlimiv.mm"
include "abssi.mm"
include "eqsstri.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "abrexex.mm"
include "simpl.mm"
include "reximi.mm"
include "ss2abi.mm"
include "elrnmpt2.mm"
include "syl6bb.mm"
include "biadan2.mm"

theorem eldiophb
  let vu: setvar u
  let vt: setvar t
  let cD: class D
  let vk: setvar k
  let cN: class N
  let vp: setvar p
  let vn: setvar n
  let vd: setvar d

  disjoint D k
  disjoint D p
  disjoint k p
  disjoint N k
  disjoint N p
  disjoint N t
  disjoint N u
  disjoint k t
  disjoint k u
  disjoint p t
  disjoint p u
  disjoint t u
  disjoint D n
  disjoint D d
  disjoint d n
  disjoint k n
  disjoint n p
  disjoint d k
  disjoint d p
  disjoint N n
  disjoint N d
  disjoint n t
  disjoint n u
  disjoint d t
  disjoint d u
  assert |- ( D e. ( Dioph ` N ) <-> ( N e. NN0 /\ E. k e. ( ZZ>= ` N ) E. p e. ( mzPoly ` ( 1 ... k ) ) D = { t | E. u e. ( NN0 ^m ( 1 ... k ) ) ( t = ( u |` ( 1 ... N ) ) /\ ( p ` u ) = 0 ) } ) )

  proof
    cD
    cN
    cdioph
    cfv
    #
    wcel
    #
    cN
    cn0
    wcel
    #
    cD
    vt
    cv
    #
    vu
    cv
    #
    c1
    cN
    cfz
    co
    #
    cres
    #
    wceq
    #
    @4
    vp
    cv
    cfv
    cc0
    wceq
    #
    wa
    #
    vu
    cn0
    c1
    vk
    cv
    #
    cfz
    co
    #
    cmap
    co
    #
    wrex
    #
    vt
    cab
    #
    wceq
    vp
    @11
    cmzp
    cfv
    #
    wrex
    vk
    cN
    cuz
    cfv
    #
    wrex
    #
    @1
    cdioph
    cdm
    cn0
    cN
    vn
    cn0
    vk
    vp
    vn
    cv
    #
    cuz
    cfv
    #
    @15
    @3
    @4
    c1
    @18
    cfz
    co
    #
    cres
    #
    wceq
    #
    @8
    wa
    #
    vu
    @12
    wrex
    #
    vt
    cab
    #
    cmpt2
    #
    crn
    #
    cdioph
    vu
    vt
    vk
    vn
    vp
    df-dioph
    #
    dmmptss
    cD
    cN
    cdioph
    elfvdm
    sseldi
    @2
    @1
    cD
    vk
    vp
    @16
    @15
    @14
    cmpt2
    #
    crn
    #
    wcel
    @17
    @2
    @0
    @30
    cD
    vn
    cN
    @27
    @30
    cn0
    cdioph
    @18
    cN
    wceq
    #
    @26
    @29
    @31
    vk
    vp
    @19
    @15
    @25
    @16
    @15
    @14
    @18
    cN
    cuz
    fveq2
    @31
    @15
    eqidd
    @31
    @24
    @13
    vt
    @31
    @23
    @9
    vu
    @12
    @31
    @22
    @7
    @8
    @31
    @21
    @6
    @3
    @31
    @20
    @5
    @4
    @18
    cN
    c1
    cfz
    oveq2
    reseq2d
    eqeq2d
    anbi1d
    rexbidv
    abbidv
    mpt2eq123dv
    rneqd
    @28
    @30
    cn0
    @5
    cmap
    co
    #
    cpw
    #
    @32
    cn0
    @5
    cmap
    ovex
    #
    pwex
    @30
    vd
    cv
    #
    @14
    wceq
    #
    vp
    @15
    wrex
    #
    vk
    @16
    wrex
    #
    vd
    cab
    @33
    vk
    vp
    vd
    @16
    @15
    @14
    @29
    @29
    eqid
    #
    rnmpt2
    @38
    vd
    @33
    @37
    @35
    @33
    wcel
    #
    vk
    @16
    @10
    @16
    wcel
    #
    @36
    @40
    vp
    @15
    @41
    @40
    @36
    @14
    @33
    wcel
    #
    @41
    @14
    @32
    wss
    @42
    @41
    @13
    vt
    @32
    @41
    @9
    @3
    @32
    wcel
    #
    vu
    @12
    @41
    @4
    @12
    wcel
    #
    wa
    #
    @43
    @9
    @6
    @32
    wcel
    #
    @45
    @5
    cn0
    @6
    wf
    #
    @46
    @44
    @11
    cn0
    @4
    wf
    @5
    @11
    wss
    @47
    @41
    @4
    cn0
    @11
    elmapi
    cN
    c1
    @10
    fzss2
    @11
    cn0
    @5
    @4
    fssres
    syl2anr
    cn0
    @5
    @6
    nn0ex
    c1
    cN
    cfz
    ovex
    elmap
    sylibr
    @7
    @43
    @46
    wb
    @8
    @3
    @6
    @32
    eleq1
    adantr
    syl5ibrcom
    rexlimdva
    abssdv
    @14
    @32
    @34
    elpw2
    sylibr
    @35
    @14
    @33
    eleq1
    syl5ibrcom
    rexlimdvw
    rexlimiv
    abssi
    eqsstri
    ssexi
    fvmpt
    eleq2d
    vk
    vp
    @16
    @15
    @14
    cD
    @29
    @39
    @14
    @7
    vu
    @12
    wrex
    #
    vt
    cab
    vu
    vt
    @12
    @6
    cn0
    @11
    cmap
    ovex
    abrexex
    @13
    @48
    vt
    @9
    @7
    vu
    @12
    @7
    @8
    simpl
    reximi
    ss2abi
    ssexi
    elrnmpt2
    syl6bb
    biadan2
end
