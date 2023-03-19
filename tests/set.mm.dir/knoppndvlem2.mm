include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cexp.mm"
include "cneg.mm"
include "cdiv.mm"
include "cmin.mm"
include "c1.mm"
include "cz.mm"
include "2cnd.mm"
include "cn.mm"
include "wcel.mm"
include "nnz.mm"
include "syl.mm"
include "zcnd.mm"
include "mulcld.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "0red.mm"
include "1red.mm"
include "zred.mm"
include "clt.mm"
include "wbr.mm"
include "0lt1.mm"
include "cle.mm"
include "nnge1.mm"
include "ltletrd.mm"
include "ltned.mm"
include "necomd.mm"
include "mulne0d.mm"
include "expclzd.mm"
include "znegcld.mm"
include "divcld.mm"
include "mulassd.mm"
include "eqcomd.mm"
include "divassd.mm"
include "caddc.mm"
include "cc.mm"
include "wa.mm"
include "wceq.mm"
include "jca.mm"
include "expaddz.mm"
include "negsubd.mm"
include "oveq2d.mm"
include "wb.mm"
include "znnsub.mm"
include "mpbid.mm"
include "expm1t.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "cn0.mm"
include "zsubcl.mm"
include "peano2zm.mm"
include "posdifd.mm"
include "0zd.mm"
include "zltlem1.mm"
include "elnn0z.mm"
include "sylibr.mm"
include "expcld.mm"
include "divcan3d.mm"
include "eqtrd.mm"
include "2z.mm"
include "zmulcl.mm"
include "zexpcl.mm"
include "zmulcld.mm"
include "eqeltrd.mm"

theorem knoppndvlem2
  let wph: wff ph
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  assume knoppndvlem2.n: |- ( ph -> N e. NN )
  assume knoppndvlem2.i: |- ( ph -> I e. ZZ )
  assume knoppndvlem2.j: |- ( ph -> J e. ZZ )
  assume knoppndvlem2.m: |- ( ph -> M e. ZZ )
  assume knoppndvlem2.1: |- ( ph -> J < I )


  assert |- ( ph -> ( ( ( 2 x. N ) ^ I ) x. ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) ) e. ZZ )

  proof
    wph
    c2
    cN
    cmul
    co
    #
    cI
    cexp
    co
    #
    @0
    cJ
    cneg
    #
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cM
    cmul
    co
    cmul
    co
    #
    @0
    cI
    cJ
    cmin
    co
    #
    c1
    cmin
    co
    #
    cexp
    co
    #
    cN
    cmul
    co
    #
    cM
    cmul
    co
    #
    cz
    wph
    @5
    @1
    @4
    cmul
    co
    #
    cM
    cmul
    co
    #
    @10
    wph
    @12
    @5
    wph
    @1
    @4
    cM
    wph
    @0
    cI
    wph
    c2
    cN
    wph
    2cnd
    #
    wph
    cN
    wph
    cN
    cn
    wcel
    #
    cN
    cz
    wcel
    #
    knoppndvlem2.n
    cN
    nnz
    syl
    #
    zcnd
    #
    mulcld
    #
    wph
    c2
    cN
    @13
    @17
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    #
    wph
    cc0
    cN
    wph
    cc0
    cN
    wph
    0red
    #
    wph
    cc0
    c1
    cN
    @20
    wph
    1red
    wph
    cN
    @16
    zred
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    wph
    @14
    c1
    cN
    cle
    wbr
    knoppndvlem2.n
    cN
    nnge1
    syl
    ltletrd
    ltned
    necomd
    mulne0d
    #
    knoppndvlem2.i
    expclzd
    #
    wph
    @3
    c2
    wph
    @0
    @2
    @18
    @21
    wph
    cJ
    knoppndvlem2.j
    znegcld
    #
    expclzd
    #
    @13
    @19
    divcld
    wph
    cM
    knoppndvlem2.m
    zcnd
    mulassd
    eqcomd
    wph
    @11
    @9
    cM
    cmul
    wph
    @11
    @1
    @3
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @8
    @0
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @9
    wph
    @26
    @11
    wph
    @1
    @3
    c2
    @22
    @24
    @13
    @19
    divassd
    eqcomd
    wph
    @25
    @27
    c2
    cdiv
    wph
    @25
    @0
    cI
    @2
    caddc
    co
    #
    cexp
    co
    #
    @0
    @6
    cexp
    co
    #
    @27
    wph
    @30
    @25
    wph
    @0
    cc
    wcel
    #
    @0
    cc0
    wne
    #
    wa
    #
    cI
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    wa
    #
    wa
    @30
    @25
    wceq
    wph
    @34
    @37
    wph
    @32
    @33
    @18
    @21
    jca
    wph
    @35
    @36
    knoppndvlem2.i
    @23
    jca
    jca
    @0
    cI
    @2
    expaddz
    syl
    eqcomd
    wph
    @29
    @6
    @0
    cexp
    wph
    cI
    cJ
    wph
    cI
    knoppndvlem2.i
    zcnd
    wph
    cJ
    knoppndvlem2.j
    zcnd
    negsubd
    oveq2d
    wph
    @32
    @6
    cn
    wcel
    #
    wa
    @31
    @27
    wceq
    wph
    @32
    @38
    @18
    wph
    cJ
    cI
    clt
    wbr
    #
    @38
    knoppndvlem2.1
    wph
    cJ
    cz
    wcel
    #
    @35
    wa
    @39
    @38
    wb
    wph
    @40
    @35
    knoppndvlem2.j
    knoppndvlem2.i
    jca
    cJ
    cI
    znnsub
    syl
    mpbid
    jca
    @0
    @6
    expm1t
    syl
    3eqtrd
    oveq1d
    wph
    @28
    @8
    @0
    c2
    cdiv
    co
    #
    cmul
    co
    @9
    wph
    @8
    @0
    c2
    wph
    @0
    @7
    @18
    wph
    @7
    cz
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    wa
    @7
    cn0
    wcel
    #
    wph
    @42
    @43
    wph
    @6
    cz
    wcel
    #
    @42
    wph
    @35
    @40
    wa
    @45
    wph
    @35
    @40
    knoppndvlem2.i
    knoppndvlem2.j
    jca
    cI
    cJ
    zsubcl
    syl
    #
    @6
    peano2zm
    syl
    wph
    cc0
    @6
    clt
    wbr
    #
    @43
    wph
    @39
    @47
    knoppndvlem2.1
    wph
    cJ
    cI
    wph
    cJ
    knoppndvlem2.j
    zred
    wph
    cI
    knoppndvlem2.i
    zred
    posdifd
    mpbid
    wph
    cc0
    cz
    wcel
    #
    @45
    wa
    @47
    @43
    wb
    wph
    @48
    @45
    wph
    0zd
    @46
    jca
    cc0
    @6
    zltlem1
    syl
    mpbid
    jca
    @7
    elnn0z
    sylibr
    #
    expcld
    @18
    @13
    @19
    divassd
    wph
    @41
    cN
    @8
    cmul
    wph
    cN
    c2
    @17
    @13
    @19
    divcan3d
    oveq2d
    eqtrd
    3eqtrd
    oveq1d
    eqtrd
    wph
    @9
    cM
    wph
    @8
    cN
    wph
    @0
    cz
    wcel
    #
    @44
    wa
    @8
    cz
    wcel
    wph
    @50
    @44
    wph
    c2
    cz
    wcel
    #
    @15
    wa
    @50
    wph
    @51
    @15
    @51
    wph
    2z
    a1i
    @16
    jca
    c2
    cN
    zmulcl
    syl
    @49
    jca
    @0
    @7
    zexpcl
    syl
    @16
    zmulcld
    knoppndvlem2.m
    zmulcld
    eqeltrd
end
