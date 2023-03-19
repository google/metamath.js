include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "ccxp.mm"
include "cexp.mm"
include "wceq.mm"
include "ci.mm"
include "cpi.mm"
include "cmul.mm"
include "ce.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc.mm"
include "cr.mm"
include "2re.mm"
include "simpl.mm"
include "nndivre.mm"
include "sylancr.mm"
include "recnd.mm"
include "ax-icn.mm"
include "picn.mm"
include "mulcli.mm"
include "a1i.mm"
include "mulcld.mm"
include "efexp.mm"
include "sylancom.mm"
include "zcn.mm"
include "adantl.mm"
include "nncn.mm"
include "adantr.mm"
include "2cn.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "div32d.mm"
include "oveq1d.mm"
include "divcld.mm"
include "mulassd.mm"
include "3eqtr3d.mm"
include "fveq2d.mm"
include "clog.mm"
include "neg1cn.mm"
include "neg1ne0.mm"
include "cxpefd.mm"
include "logm1.mm"
include "oveq2i.mm"
include "fveq2i.mm"
include "syl6eq.mm"
include "3eqtr4rd.mm"
include "eqeq1d.mm"
include "wb.mm"
include "mulcl.mm"
include "sylancl.mm"
include "efeq1.mm"
include "syl.mm"
include "mul12i.mm"
include "2ne0.mm"
include "ine0.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "mulne0i.mm"
include "divcan4d.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "nnz.mm"
include "simpr.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "bitr4d.mm"
include "3bitrd.mm"

theorem root1eq1
  let cK: class K
  let cN: class N


  assert |- ( ( N e. NN /\ K e. ZZ ) -> ( ( ( -u 1 ^c ( 2 / N ) ) ^ K ) = 1 <-> N || K ) )

  proof
    cN
    cn
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    c1
    cneg
    #
    c2
    cN
    cdiv
    co
    #
    ccxp
    co
    #
    cK
    cexp
    co
    #
    c1
    wceq
    cK
    cN
    cdiv
    co
    #
    c2
    ci
    cpi
    cmul
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    c1
    wceq
    #
    @10
    ci
    c2
    cpi
    cmul
    co
    cmul
    co
    #
    cdiv
    co
    #
    cz
    wcel
    #
    cN
    cK
    cdvds
    wbr
    #
    @2
    @6
    @11
    c1
    @2
    cK
    @4
    @8
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    @17
    ce
    cfv
    #
    cK
    cexp
    co
    #
    @11
    @6
    @0
    @1
    @17
    cc
    wcel
    @19
    @21
    wceq
    @2
    @4
    @8
    @2
    @4
    @2
    c2
    cr
    wcel
    @0
    @4
    cr
    wcel
    2re
    @0
    @1
    simpl
    c2
    cN
    nndivre
    sylancr
    recnd
    #
    @8
    cc
    wcel
    @2
    ci
    cpi
    ax-icn
    picn
    mulcli
    #
    a1i
    #
    mulcld
    @17
    cK
    efexp
    sylancom
    @2
    @10
    @18
    ce
    @2
    @7
    c2
    cmul
    co
    #
    @8
    cmul
    co
    cK
    @4
    cmul
    co
    #
    @8
    cmul
    co
    @10
    @18
    @2
    @25
    @26
    @8
    cmul
    @2
    cK
    cN
    c2
    @1
    cK
    cc
    wcel
    @0
    cK
    zcn
    adantl
    #
    @0
    cN
    cc
    wcel
    @1
    cN
    nncn
    adantr
    #
    c2
    cc
    wcel
    @2
    2cn
    a1i
    #
    @0
    cN
    cc0
    wne
    #
    @1
    cN
    nnne0
    adantr
    #
    div32d
    oveq1d
    @2
    @7
    c2
    @8
    @2
    cK
    cN
    @27
    @28
    @31
    divcld
    #
    @29
    @24
    mulassd
    @2
    cK
    @4
    @8
    @27
    @22
    @24
    mulassd
    3eqtr3d
    fveq2d
    @2
    @5
    @20
    cK
    cexp
    @2
    @5
    @4
    @3
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    @20
    @2
    @3
    @4
    @3
    cc
    wcel
    @2
    neg1cn
    a1i
    @3
    cc0
    wne
    @2
    neg1ne0
    a1i
    @22
    cxpefd
    @34
    @17
    ce
    @33
    @8
    @4
    cmul
    logm1
    oveq2i
    fveq2i
    syl6eq
    oveq1d
    3eqtr4rd
    eqeq1d
    @2
    @10
    cc
    wcel
    #
    @12
    @15
    wb
    @2
    @7
    cc
    wcel
    @9
    cc
    wcel
    #
    @35
    @32
    c2
    @8
    2cn
    @23
    mulcli
    #
    @7
    @9
    mulcl
    sylancl
    @10
    efeq1
    syl
    @2
    @15
    @7
    cz
    wcel
    #
    @16
    @2
    @14
    @7
    cz
    @2
    @14
    @10
    @9
    cdiv
    co
    @7
    @13
    @9
    @10
    cdiv
    ci
    c2
    cpi
    ax-icn
    2cn
    picn
    mul12i
    oveq2i
    @2
    @7
    @9
    @32
    @36
    @2
    @37
    a1i
    @9
    cc0
    wne
    @2
    c2
    @8
    2cn
    @23
    2ne0
    ci
    cpi
    ax-icn
    picn
    ine0
    cpi
    pire
    pipos
    gt0ne0ii
    mulne0i
    mulne0i
    a1i
    divcan4d
    syl5eq
    eleq1d
    @2
    cN
    cz
    wcel
    #
    @30
    @1
    @16
    @38
    wb
    @0
    @39
    @1
    cN
    nnz
    adantr
    @31
    @0
    @1
    simpr
    cN
    cK
    dvdsval2
    syl3anc
    bitr4d
    3bitrd
end
