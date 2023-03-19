include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "cn.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "ciun.mm"
include "ccom.mm"
include "cun.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "dftrcl3.mm"
include "nnex.mm"
include "ovex.mm"
include "iunex.mm"
include "fvmpt.mm"
include "syl.mm"
include "c1.mm"
include "c2.mm"
include "cuz.mm"
include "csn.mm"
include "cmin.mm"
include "cfz.mm"
include "nnuz.mm"
include "2eluzge1.mm"
include "uzsplit.mm"
include "ax-mp.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "cz.mm"
include "1z.mm"
include "fzsn.mm"
include "eqtri.mm"
include "uneq1i.mm"
include "3eqtri.mm"
include "iuneq1.mm"
include "iunxun.mm"
include "1ex.mm"
include "oveq2.mm"
include "iunxsn.mm"
include "relexp1g.mm"
include "coeq1d.mm"
include "coiun1.mm"
include "caddc.mm"
include "uz2m1nn.mm"
include "adantl.mm"
include "eluzp1p1.mm"
include "eleq2s.mm"
include "1p1e2.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "relexpsucnnr.mm"
include "eqcomd.mm"
include "sylan2.mm"
include "wb.mm"
include "cc.mm"
include "eluzelcn.mm"
include "npcan1.mm"
include "3syl.mm"
include "eqeq1d.mm"
include "mpbid.mm"
include "cbviuneq12dv.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "uneq12d.mm"

theorem trclfvdecomr
  let cR: class R
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r


  assert |- ( R e. V -> ( t+ ` R ) = ( R u. ( ( t+ ` R ) o. R ) ) )

  proof
    cR
    cV
    wcel
    #
    cR
    ctcl
    cfv
    #
    vn
    cn
    cR
    vn
    cv
    #
    crelexp
    co
    #
    ciun
    #
    cR
    @1
    cR
    ccom
    #
    cun
    #
    @0
    cR
    cvv
    wcel
    #
    @1
    @4
    wceq
    cR
    cV
    elex
    #
    vr
    cR
    vn
    cn
    vr
    cv
    #
    @2
    crelexp
    co
    #
    ciun
    @4
    cvv
    ctcl
    @9
    cR
    wceq
    #
    vn
    cn
    @10
    @3
    @9
    cR
    @2
    crelexp
    oveq1
    iuneq2d
    vn
    vr
    dftrcl3
    vn
    cn
    @3
    nnex
    cR
    @2
    crelexp
    ovex
    iunex
    fvmpt
    syl
    @0
    @4
    cR
    c1
    crelexp
    co
    #
    vn
    c2
    cuz
    cfv
    #
    @3
    ciun
    #
    cun
    #
    @6
    @4
    vn
    c1
    csn
    #
    @13
    cun
    #
    @3
    ciun
    #
    vn
    @16
    @3
    ciun
    #
    @14
    cun
    @15
    cn
    @17
    wceq
    @4
    @18
    wceq
    cn
    c1
    cuz
    cfv
    #
    c1
    c2
    c1
    cmin
    co
    #
    cfz
    co
    #
    @13
    cun
    #
    @17
    nnuz
    c2
    @20
    wcel
    @20
    @23
    wceq
    2eluzge1
    c1
    c2
    uzsplit
    ax-mp
    @22
    @16
    @13
    @22
    c1
    c1
    cfz
    co
    #
    @16
    @21
    c1
    c1
    cfz
    2m1e1
    oveq2i
    c1
    cz
    wcel
    @24
    @16
    wceq
    1z
    c1
    fzsn
    ax-mp
    eqtri
    uneq1i
    3eqtri
    vn
    cn
    @17
    @3
    iuneq1
    ax-mp
    vn
    @16
    @13
    @3
    iunxun
    @19
    @12
    @14
    vn
    c1
    @3
    @12
    1ex
    @2
    c1
    cR
    crelexp
    oveq2
    iunxsn
    uneq1i
    3eqtri
    @0
    @12
    cR
    @14
    @5
    cR
    cV
    relexp1g
    @0
    @5
    @14
    @0
    @5
    vm
    cn
    cR
    vm
    cv
    #
    crelexp
    co
    #
    ciun
    #
    cR
    ccom
    #
    @14
    @0
    @1
    @27
    cR
    @0
    @7
    @1
    @27
    wceq
    @8
    vr
    cR
    vm
    cn
    @9
    @25
    crelexp
    co
    #
    ciun
    @27
    cvv
    ctcl
    @11
    vm
    cn
    @29
    @26
    @9
    cR
    @25
    crelexp
    oveq1
    iuneq2d
    vm
    vr
    dftrcl3
    vm
    cn
    @26
    nnex
    cR
    @25
    crelexp
    ovex
    iunex
    fvmpt
    syl
    coeq1d
    @0
    @28
    vm
    cn
    @26
    cR
    ccom
    #
    ciun
    @14
    vm
    @26
    cR
    cn
    coiun1
    @0
    vm
    vn
    cn
    @30
    @13
    @3
    cR
    @2
    c1
    cmin
    co
    #
    crelexp
    co
    #
    cR
    ccom
    #
    cR
    @25
    c1
    caddc
    co
    #
    crelexp
    co
    #
    @31
    @34
    @2
    @13
    wcel
    #
    @31
    cn
    wcel
    #
    @0
    @2
    uz2m1nn
    #
    adantl
    @25
    cn
    wcel
    #
    @34
    @13
    wcel
    @0
    @39
    @34
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @13
    @34
    @41
    wcel
    @25
    @20
    cn
    c1
    @25
    eluzp1p1
    nnuz
    eleq2s
    @40
    c2
    cuz
    1p1e2
    fveq2i
    syl6eleq
    adantl
    @25
    @31
    wceq
    #
    @0
    @30
    @33
    wceq
    @36
    @42
    @26
    @32
    cR
    @25
    @31
    cR
    crelexp
    oveq2
    coeq1d
    3ad2ant3
    @2
    @34
    wceq
    @0
    @3
    @35
    wceq
    @39
    @2
    @34
    cR
    crelexp
    oveq2
    3ad2ant3
    @0
    @39
    wa
    @35
    @30
    cR
    @25
    cV
    relexpsucnnr
    eqcomd
    @0
    @36
    wa
    cR
    @31
    c1
    caddc
    co
    #
    crelexp
    co
    #
    @33
    wceq
    #
    @3
    @33
    wceq
    #
    @36
    @0
    @37
    @45
    @38
    cR
    @31
    cV
    relexpsucnnr
    sylan2
    @36
    @45
    @46
    wb
    @0
    @36
    @44
    @3
    @33
    @36
    @2
    cc
    wcel
    @43
    @2
    wceq
    @44
    @3
    wceq
    c2
    @2
    eluzelcn
    @2
    npcan1
    @43
    @2
    cR
    crelexp
    oveq2
    3syl
    eqeq1d
    adantl
    mpbid
    cbviuneq12dv
    syl5eq
    eqtrd
    eqcomd
    uneq12d
    syl5eq
    eqtrd
end
