include "cngp.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "w3a.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "csn.mm"
include "cxp.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "cnm.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cnghm.mm"
include "cr.mm"
include "id.mm"
include "0re.mm"
include "syl6eqel.mm"
include "isnghm2.mm"
include "biimpar.mm"
include "sylan2.mm"
include "eqid.mm"
include "nmoi.mm"
include "sylan.mm"
include "simplr.mm"
include "oveq1d.mm"
include "simpl1.mm"
include "nmcl.mm"
include "recnd.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "cbs.mm"
include "simpll2.mm"
include "wf.mm"
include "simpl3.mm"
include "ghmf.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "nmge0.mm"
include "syl2anc.mm"
include "wb.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "nmeq0.mm"
include "mpbid.mm"
include "mpteq2dva.mm"
include "feqmptd.mm"
include "fconstmpt.mm"
include "a1i.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "nmo0.mm"
include "3adant3.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem nmoeq0
  let cS: class S
  let cT: class T
  let cF: class F
  let cN: class N
  let cV: class V
  let c.0: class .0.
  let vx: setvar x
  assume nmo0.1: |- N = ( S normOp T )
  assume nmo0.2: |- V = ( Base ` S )
  assume nmo0.3: |- .0. = ( 0g ` T )


  assert |- ( ( S e. NrmGrp /\ T e. NrmGrp /\ F e. ( S GrpHom T ) ) -> ( ( N ` F ) = 0 <-> F = ( V X. { .0. } ) ) )

  proof
    cS
    cngp
    wcel
    #
    cT
    cngp
    wcel
    #
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    w3a
    #
    cF
    cN
    cfv
    #
    cc0
    wceq
    #
    cF
    cV
    c.0
    csn
    cxp
    #
    wceq
    #
    @3
    @5
    @7
    @3
    @5
    wa
    #
    vx
    cV
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    vx
    cV
    c.0
    cmpt
    #
    cF
    @6
    @8
    vx
    cV
    @10
    c.0
    @8
    @9
    cV
    wcel
    #
    wa
    #
    @10
    cT
    cnm
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    @10
    c.0
    wceq
    #
    @13
    @16
    @15
    cc0
    cle
    wbr
    #
    cc0
    @15
    cle
    wbr
    #
    @13
    @15
    @4
    @9
    cS
    cnm
    cfv
    #
    cfv
    #
    cmul
    co
    #
    cc0
    cle
    @8
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    @12
    @15
    @22
    cle
    wbr
    @5
    @3
    @4
    cr
    wcel
    #
    @23
    @5
    @4
    cc0
    cr
    @5
    id
    0re
    syl6eqel
    @3
    @23
    @24
    cS
    cT
    cF
    cN
    nmo0.1
    isnghm2
    biimpar
    sylan2
    cS
    cT
    cF
    @20
    @14
    cN
    cV
    @9
    nmo0.1
    nmo0.2
    @20
    eqid
    #
    @14
    eqid
    #
    nmoi
    sylan
    @13
    @22
    cc0
    @21
    cmul
    co
    cc0
    @13
    @4
    cc0
    @21
    cmul
    @3
    @5
    @12
    simplr
    oveq1d
    @13
    @21
    @13
    @21
    @8
    @0
    @12
    @21
    cr
    wcel
    @0
    @1
    @2
    @5
    simpl1
    @9
    cS
    @20
    cV
    nmo0.2
    @25
    nmcl
    sylan
    recnd
    mul02d
    eqtrd
    breqtrd
    @13
    @1
    @10
    cT
    cbs
    cfv
    #
    wcel
    #
    @19
    @0
    @1
    @2
    @5
    @12
    simpll2
    #
    @8
    cV
    @27
    @9
    cF
    @8
    @2
    cV
    @27
    cF
    wf
    @0
    @1
    @2
    @5
    simpl3
    cS
    cT
    cF
    cV
    @27
    nmo0.2
    @27
    eqid
    #
    ghmf
    syl
    #
    ffvelrnda
    #
    @10
    cT
    @14
    @27
    @30
    @26
    nmge0
    syl2anc
    @13
    @15
    cr
    wcel
    #
    cc0
    cr
    wcel
    @16
    @18
    @19
    wa
    wb
    @13
    @1
    @28
    @33
    @29
    @32
    @10
    cT
    @14
    @27
    @30
    @26
    nmcl
    syl2anc
    0re
    @15
    cc0
    letri3
    sylancl
    mpbir2and
    @13
    @1
    @28
    @16
    @17
    wb
    @29
    @32
    @10
    cT
    @14
    @27
    c.0
    @30
    @26
    nmo0.3
    nmeq0
    syl2anc
    mpbid
    mpteq2dva
    @8
    vx
    cV
    @27
    cF
    @31
    feqmptd
    @6
    @11
    wceq
    @8
    vx
    cV
    c.0
    fconstmpt
    a1i
    3eqtr4d
    ex
    @3
    @5
    @7
    @6
    cN
    cfv
    #
    cc0
    wceq
    #
    @0
    @1
    @35
    @2
    cS
    cT
    cN
    cV
    c.0
    nmo0.1
    nmo0.2
    nmo0.3
    nmo0
    3adant3
    @7
    @4
    @34
    cc0
    cF
    @6
    cN
    fveq2
    eqeq1d
    syl5ibrcom
    impbid
end
