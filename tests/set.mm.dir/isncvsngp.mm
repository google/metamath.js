include "ccvs.mm"
include "wcel.mm"
include "cnvc.mm"
include "wa.mm"
include "cngp.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "wceq.mm"
include "wral.mm"
include "cin.mm"
include "w3a.mm"
include "clvec.mm"
include "cnlm.mm"
include "wb.mm"
include "isnvc.mm"
include "ancom.mm"
include "bitri.mm"
include "a1i.mm"
include "id.mm"
include "cvslvec.mm"
include "biantrurd.mm"
include "cclm.mm"
include "cvsclm.mm"
include "clmod.mm"
include "cnrg.mm"
include "cnm.mm"
include "eqid.mm"
include "isnlm.mm"
include "3anass.mm"
include "anbi1i.mm"
include "anass.mm"
include "clmlmod.mm"
include "ccnfld.mm"
include "cress.mm"
include "clmsca.mm"
include "csubrg.mm"
include "cnnrg.mm"
include "clmsubrg.mm"
include "subrgnrg.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "jca.mm"
include "ralcom.mm"
include "cres.mm"
include "fveq2d.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "subgnm.mm"
include "3syl.mm"
include "eqtrd.mm"
include "adantr.mm"
include "fveq1d.mm"
include "cnfldnm.mm"
include "eqcomi.mm"
include "reseq1i.mm"
include "fveq1i.mm"
include "fvres.mm"
include "ad2antll.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "2ralbidva.mm"
include "syl5bb.mm"
include "anbi2d.mm"
include "3bitr2d.mm"
include "syl.mm"
include "pm5.32i.mm"
include "elin.mm"
include "3bitr4i.mm"

theorem isncvsngp
  let vx: setvar x
  let c.x: class .x.
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  assume isncvsngp.v: |- V = ( Base ` W )
  assume isncvsngp.n: |- N = ( norm ` W )
  assume isncvsngp.s: |- .x. = ( .s ` W )
  assume isncvsngp.f: |- F = ( Scalar ` W )
  assume isncvsngp.k: |- K = ( Base ` F )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint K k
  disjoint K x
  disjoint N k
  disjoint N x
  disjoint V k
  disjoint V x
  disjoint W k
  disjoint W x
  disjoint .x. k
  disjoint .x. x
  assert |- ( W e. ( NrmVec i^i CVec ) <-> ( W e. CVec /\ W e. NrmGrp /\ A. x e. V A. k e. K ( N ` ( k .x. x ) ) = ( ( abs ` k ) x. ( N ` x ) ) ) )

  proof
    cW
    ccvs
    wcel
    #
    cW
    cnvc
    wcel
    #
    wa
    #
    @0
    cW
    cngp
    wcel
    #
    vk
    cv
    #
    vx
    cv
    #
    c.x
    co
    cN
    cfv
    #
    @4
    cabs
    cfv
    #
    @5
    cN
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vk
    cK
    wral
    vx
    cV
    wral
    #
    wa
    #
    wa
    cW
    cnvc
    ccvs
    cin
    wcel
    #
    @0
    @3
    @11
    w3a
    @0
    @1
    @12
    @0
    @1
    cW
    clvec
    wcel
    #
    cW
    cnlm
    wcel
    #
    wa
    #
    @15
    @12
    @1
    @16
    wb
    @0
    @1
    @15
    @14
    wa
    @16
    cW
    isnvc
    @15
    @14
    ancom
    bitri
    a1i
    @0
    @14
    @15
    @0
    cW
    @0
    id
    #
    cvslvec
    biantrurd
    @0
    cW
    cclm
    wcel
    #
    @15
    @12
    wb
    @0
    cW
    @17
    cvsclm
    @15
    @3
    cW
    clmod
    wcel
    #
    cF
    cnrg
    wcel
    #
    w3a
    #
    @6
    @4
    cF
    cnm
    cfv
    #
    cfv
    #
    @8
    cmul
    co
    #
    wceq
    #
    vx
    cV
    wral
    vk
    cK
    wral
    #
    wa
    #
    @18
    @12
    vk
    vx
    @22
    c.x
    cF
    cK
    cN
    cV
    cW
    isncvsngp.v
    isncvsngp.n
    isncvsngp.s
    isncvsngp.f
    isncvsngp.k
    @22
    eqid
    isnlm
    @18
    @27
    @19
    @20
    wa
    #
    @3
    @26
    wa
    #
    wa
    #
    @29
    @12
    @27
    @30
    wb
    @18
    @27
    @28
    @3
    wa
    #
    @26
    wa
    @30
    @21
    @31
    @26
    @21
    @3
    @28
    wa
    @31
    @3
    @19
    @20
    3anass
    @3
    @28
    ancom
    bitri
    anbi1i
    @28
    @3
    @26
    anass
    bitri
    a1i
    @18
    @28
    @29
    @18
    @19
    @20
    cW
    clmlmod
    @18
    cF
    ccnfld
    cK
    cress
    co
    #
    cnrg
    cF
    cK
    cW
    isncvsngp.f
    isncvsngp.k
    clmsca
    #
    @18
    ccnfld
    cnrg
    wcel
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    @32
    cnrg
    wcel
    cnnrg
    cF
    cK
    cW
    isncvsngp.f
    isncvsngp.k
    clmsubrg
    #
    cK
    ccnfld
    @32
    @32
    eqid
    #
    subrgnrg
    sylancr
    eqeltrd
    jca
    biantrurd
    @18
    @26
    @11
    @3
    @26
    @25
    vk
    cK
    wral
    vx
    cV
    wral
    @18
    @11
    @25
    vk
    vx
    cK
    cV
    ralcom
    @18
    @25
    @10
    vx
    vk
    cV
    cK
    @18
    @5
    cV
    wcel
    #
    @4
    cK
    wcel
    #
    wa
    #
    wa
    #
    @24
    @9
    @6
    @40
    @23
    @7
    @8
    cmul
    @40
    @23
    @4
    ccnfld
    cnm
    cfv
    #
    cK
    cres
    #
    cfv
    #
    @7
    @40
    @4
    @22
    @42
    @18
    @22
    @42
    wceq
    @39
    @18
    @22
    @32
    cnm
    cfv
    #
    @42
    @18
    cF
    @32
    cnm
    @33
    fveq2d
    @18
    @34
    cK
    ccnfld
    csubg
    cfv
    wcel
    @44
    @42
    wceq
    @35
    cK
    ccnfld
    subrgsubg
    cK
    ccnfld
    @32
    @44
    @41
    @36
    @41
    eqid
    @44
    eqid
    subgnm
    3syl
    eqtrd
    adantr
    fveq1d
    @40
    @43
    @4
    cabs
    cK
    cres
    #
    cfv
    #
    @7
    @4
    @42
    @45
    @41
    cabs
    cK
    cabs
    @41
    cnfldnm
    eqcomi
    reseq1i
    fveq1i
    @38
    @46
    @7
    wceq
    @18
    @37
    @4
    cK
    cabs
    fvres
    ad2antll
    syl5eq
    eqtrd
    oveq1d
    eqeq2d
    2ralbidva
    syl5bb
    anbi2d
    3bitr2d
    syl5bb
    syl
    3bitr2d
    pm5.32i
    @13
    @1
    @0
    wa
    @2
    cW
    cnvc
    ccvs
    elin
    @1
    @0
    ancom
    bitri
    @0
    @3
    @11
    3anass
    3bitr4i
end
