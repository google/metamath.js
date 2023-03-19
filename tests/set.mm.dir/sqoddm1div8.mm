include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cexp.mm"
include "cmin.mm"
include "c8.mm"
include "cdiv.mm"
include "c4.mm"
include "oveq1.mm"
include "cc.mm"
include "2z.mm"
include "a1i.mm"
include "id.mm"
include "zmulcld.mm"
include "zcnd.mm"
include "binom21.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "2cnd.mm"
include "zcn.mm"
include "sqmuld.mm"
include "sq2.mm"
include "eqtrd.mm"
include "w3a.mm"
include "mulass.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "2t2e4.mm"
include "oveq12d.mm"
include "4z.mm"
include "zsqcl.mm"
include "addcld.mm"
include "pncan1.mm"
include "adantr.mm"
include "4cn.mm"
include "adddid.mm"
include "4t2e8.mm"
include "oveq2d.mm"
include "cc0.mm"
include "wne.mm"
include "zaddcld.mm"
include "2cnne0.mm"
include "4ne0.mm"
include "pm3.2i.mm"
include "divcan5.mm"
include "sqvald.mm"
include "mulid1d.mm"
include "1cnd.mm"
include "adddi.mm"
include "3eqtrd.mm"

theorem sqoddm1div8
  let cM: class M
  let cN: class N


  assert |- ( ( N e. ZZ /\ M = ( ( 2 x. N ) + 1 ) ) -> ( ( ( M ^ 2 ) - 1 ) / 8 ) = ( ( N x. ( N + 1 ) ) / 2 ) )

  proof
    cN
    cz
    wcel
    #
    cM
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    cM
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c8
    cdiv
    co
    c4
    cN
    c2
    cexp
    co
    #
    cmul
    co
    #
    c4
    cN
    cmul
    co
    #
    caddc
    co
    #
    c8
    cdiv
    co
    #
    c4
    @7
    cN
    caddc
    co
    #
    cmul
    co
    #
    c8
    cdiv
    co
    #
    cN
    cN
    c1
    caddc
    co
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @4
    @6
    @10
    c8
    cdiv
    @4
    @6
    @1
    c2
    cexp
    co
    #
    c2
    @1
    cmul
    co
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    @10
    @4
    @5
    @20
    c1
    cmin
    @3
    @0
    @5
    @2
    c2
    cexp
    co
    #
    @20
    cM
    @2
    c2
    cexp
    oveq1
    @0
    @1
    cc
    wcel
    @22
    @20
    wceq
    @0
    @1
    @0
    c2
    cN
    c2
    cz
    wcel
    @0
    2z
    a1i
    @0
    id
    #
    zmulcld
    zcnd
    @1
    binom21
    syl
    sylan9eqr
    oveq1d
    @0
    @21
    @10
    wceq
    @3
    @0
    @21
    @10
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    @10
    @0
    @20
    @24
    c1
    cmin
    @0
    @19
    @10
    c1
    caddc
    @0
    @17
    @8
    @18
    @9
    caddc
    @0
    @17
    c2
    c2
    cexp
    co
    #
    @7
    cmul
    co
    @8
    @0
    c2
    cN
    @0
    2cnd
    #
    cN
    zcn
    #
    sqmuld
    @0
    @26
    c4
    @7
    cmul
    @26
    c4
    wceq
    @0
    sq2
    a1i
    oveq1d
    eqtrd
    @0
    @18
    c2
    c2
    cmul
    co
    #
    cN
    cmul
    co
    #
    @9
    @0
    c2
    cc
    wcel
    #
    @31
    cN
    cc
    wcel
    #
    @18
    @30
    wceq
    @27
    @27
    @28
    @31
    @31
    @32
    w3a
    @30
    @18
    c2
    c2
    cN
    mulass
    eqcomd
    syl3anc
    @0
    @29
    c4
    cN
    cmul
    @29
    c4
    wceq
    @0
    2t2e4
    a1i
    oveq1d
    eqtrd
    oveq12d
    oveq1d
    oveq1d
    @0
    @10
    cc
    wcel
    @25
    @10
    wceq
    @0
    @8
    @9
    @0
    @8
    @0
    c4
    @7
    c4
    cz
    wcel
    @0
    4z
    a1i
    #
    cN
    zsqcl
    #
    zmulcld
    zcnd
    @0
    @9
    @0
    c4
    cN
    @33
    @23
    zmulcld
    zcnd
    addcld
    @10
    pncan1
    syl
    eqtrd
    adantr
    eqtrd
    oveq1d
    @0
    @11
    @14
    wceq
    @3
    @0
    @10
    @13
    c8
    cdiv
    @0
    @13
    @10
    @0
    c4
    @7
    cN
    c4
    cc
    wcel
    #
    @0
    4cn
    a1i
    @0
    @7
    @34
    zcnd
    @28
    adddid
    eqcomd
    oveq1d
    adantr
    @0
    @14
    @16
    wceq
    @3
    @0
    @14
    @13
    c4
    c2
    cmul
    co
    #
    cdiv
    co
    #
    @12
    c2
    cdiv
    co
    #
    @16
    @0
    c8
    @36
    @13
    cdiv
    @0
    @36
    c8
    @36
    c8
    wceq
    @0
    4t2e8
    a1i
    eqcomd
    oveq2d
    @0
    @12
    cc
    wcel
    @31
    c2
    cc0
    wne
    wa
    #
    @35
    c4
    cc0
    wne
    #
    wa
    #
    @37
    @38
    wceq
    @0
    @12
    @0
    @7
    cN
    @34
    @23
    zaddcld
    zcnd
    @39
    @0
    2cnne0
    a1i
    @41
    @0
    @35
    @40
    4cn
    4ne0
    pm3.2i
    a1i
    @12
    c2
    c4
    divcan5
    syl3anc
    @0
    @12
    @15
    c2
    cdiv
    @0
    @12
    cN
    cN
    cmul
    co
    #
    cN
    caddc
    co
    @42
    cN
    c1
    cmul
    co
    #
    caddc
    co
    #
    @15
    @0
    @7
    @42
    cN
    caddc
    @0
    cN
    @28
    sqvald
    oveq1d
    @0
    cN
    @43
    @42
    caddc
    @0
    @43
    cN
    @0
    cN
    @28
    mulid1d
    eqcomd
    oveq2d
    @0
    @32
    @32
    c1
    cc
    wcel
    #
    @44
    @15
    wceq
    @28
    @28
    @0
    1cnd
    @32
    @32
    @45
    w3a
    @15
    @44
    cN
    cN
    c1
    adddi
    eqcomd
    syl3anc
    3eqtrd
    oveq1d
    3eqtrd
    adantr
    3eqtrd
end
