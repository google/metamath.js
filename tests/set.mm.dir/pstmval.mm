include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "cmetid.mm"
include "cqs.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "cmpt2.mm"
include "crn.mm"
include "cpstm.mm"
include "cvv.mm"
include "cmpt.mm"
include "df-pstm.mm"
include "a1i.mm"
include "wa.mm"
include "psmetdmdm.mm"
include "adantr.mm"
include "dmeq.mm"
include "dmeqd.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "qseq1.mm"
include "syl.mm"
include "fveq2.mm"
include "syl6reqr.mm"
include "qseq2.mm"
include "eqtr2d.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "w3a.mm"
include "simp1r.mm"
include "oveqd.mm"
include "eqeq2d.mm"
include "2rexbidv.mm"
include "abbidv.mm"
include "unieqd.mm"
include "mpt2eq3dva.mm"
include "eqtrd.mm"
include "elfvdm.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "mpancom.mm"
include "wfun.mm"
include "wb.mm"
include "cc0.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cxr.mm"
include "cxp.mm"
include "cmap.mm"
include "crab.mm"
include "df-psmet.mm"
include "funmpt2.mm"
include "elunirn.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "elfvex.mm"
include "qsexg.mm"
include "mpt2exga.mm"
include "fvmptd.mm"

theorem pstmval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let c.sm: class .~
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume pstmval.1: |- .~ = ( ~Met ` D )

  disjoint a b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint D a
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint D b
  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint X a
  disjoint X b
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint .~ a
  disjoint .~ b
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint D c
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint X c
  disjoint X d
  disjoint .~ c
  disjoint .~ d
  assert |- ( D e. ( PsMet ` X ) -> ( pstoMet ` D ) = ( a e. ( X /. .~ ) , b e. ( X /. .~ ) |-> U. { z | E. x e. a E. y e. b z = ( x D y ) } ) )

  proof
    cD
    cX
    cpsmet
    cfv
    #
    wcel
    #
    vd
    cD
    va
    vb
    vd
    cv
    #
    cdm
    #
    cdm
    #
    @2
    cmetid
    cfv
    #
    cqs
    #
    @6
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    @2
    co
    #
    wceq
    #
    vy
    vb
    cv
    #
    wrex
    vx
    va
    cv
    #
    wrex
    #
    vz
    cab
    #
    cuni
    #
    cmpt2
    #
    va
    vb
    cX
    c.sm
    cqs
    #
    @18
    @7
    @8
    @9
    cD
    co
    #
    wceq
    #
    vy
    @12
    wrex
    vx
    @13
    wrex
    #
    vz
    cab
    #
    cuni
    #
    cmpt2
    #
    cpsmet
    crn
    cuni
    #
    cpstm
    cvv
    cpstm
    vd
    @25
    @17
    cmpt
    wceq
    @1
    vx
    vy
    vz
    va
    vb
    vd
    df-pstm
    a1i
    @1
    @2
    cD
    wceq
    #
    wa
    #
    @17
    va
    vb
    @18
    @18
    @16
    cmpt2
    #
    @24
    @27
    @6
    @18
    wceq
    #
    @29
    @17
    @28
    wceq
    @27
    @18
    @4
    c.sm
    cqs
    #
    @6
    @27
    cX
    @4
    wceq
    @18
    @30
    wceq
    @27
    cX
    cD
    cdm
    #
    cdm
    #
    @4
    @1
    cX
    @32
    wceq
    @26
    cD
    cX
    psmetdmdm
    adantr
    @26
    @4
    @32
    wceq
    @1
    @26
    @3
    @31
    @2
    cD
    dmeq
    dmeqd
    adantl
    eqtr4d
    cX
    @4
    c.sm
    qseq1
    syl
    @26
    @30
    @6
    wceq
    #
    @1
    @26
    c.sm
    @5
    wceq
    @33
    @26
    @5
    cD
    cmetid
    cfv
    c.sm
    @2
    cD
    cmetid
    fveq2
    pstmval.1
    syl6reqr
    c.sm
    @5
    @4
    qseq2
    syl
    adantl
    eqtr2d
    #
    @34
    va
    vb
    @6
    @6
    @18
    @18
    @16
    mpt2eq12
    syl2anc
    @27
    va
    vb
    @18
    @18
    @16
    @23
    @27
    @13
    @18
    wcel
    #
    @12
    @18
    wcel
    #
    w3a
    #
    @15
    @22
    @37
    @14
    @21
    vz
    @37
    @11
    @20
    vx
    vy
    @13
    @12
    @37
    @10
    @19
    @7
    @37
    @2
    cD
    @8
    @9
    @1
    @26
    @35
    @36
    simp1r
    oveqd
    eqeq2d
    2rexbidv
    abbidv
    unieqd
    mpt2eq3dva
    eqtrd
    @1
    cD
    @8
    cpsmet
    cfv
    #
    wcel
    #
    vx
    cpsmet
    cdm
    #
    wrex
    #
    cD
    @25
    wcel
    #
    cX
    @40
    wcel
    @1
    @41
    cD
    cX
    cpsmet
    elfvdm
    @39
    @1
    vx
    cX
    @40
    @8
    cX
    wceq
    @38
    @0
    cD
    @8
    cX
    cpsmet
    fveq2
    eleq2d
    rspcev
    mpancom
    cpsmet
    wfun
    @42
    @41
    wb
    vx
    cvv
    @13
    @13
    @2
    co
    cc0
    wceq
    @13
    @12
    @2
    co
    vc
    cv
    #
    @13
    @2
    co
    @43
    @12
    @2
    co
    cxad
    co
    cle
    wbr
    vc
    @8
    wral
    vb
    @8
    wral
    wa
    va
    @8
    wral
    vd
    cxr
    @8
    @8
    cxp
    cmap
    co
    crab
    cpsmet
    vx
    va
    vb
    vc
    vd
    df-psmet
    funmpt2
    vx
    cD
    cpsmet
    elunirn
    ax-mp
    sylibr
    @1
    @18
    cvv
    wcel
    #
    @44
    @24
    cvv
    wcel
    @1
    cX
    cvv
    wcel
    @44
    cD
    cX
    cpsmet
    elfvex
    cX
    c.sm
    cvv
    qsexg
    syl
    #
    @45
    va
    vb
    @18
    @18
    @23
    cvv
    cvv
    mpt2exga
    syl2anc
    fvmptd
end
