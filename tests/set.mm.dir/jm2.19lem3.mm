include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cn0.mm"
include "crmy.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "caddc.mm"
include "wb.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "bibi2d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antrl.mm"
include "mul02d.mm"
include "ad2antll.mm"
include "addid1d.mm"
include "eqtr2d.mm"
include "w3a.mm"
include "simp3.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "nn0z.mm"
include "adantr.mm"
include "zmulcld.mm"
include "zaddcld.mm"
include "jm2.19lem2.mm"
include "syl3anc.mm"
include "zcnd.mm"
include "addassd.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "adddird.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "bitrd.mm"
include "3adant3.mm"
include "3exp.mm"
include "a2d.mm"
include "nn0ind.mm"
include "com12.mm"
include "3impia.mm"

theorem jm2.19lem3
  let cA: class A
  let cI: class I
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ ( M e. ZZ /\ N e. ZZ ) /\ I e. NN0 ) -> ( ( A rmY M ) || ( A rmY N ) <-> ( A rmY M ) || ( A rmY ( N + ( I x. M ) ) ) ) )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cI
    cn0
    wcel
    #
    cA
    cM
    crmy
    co
    #
    cA
    cN
    crmy
    co
    #
    cdvds
    wbr
    #
    @5
    cA
    cN
    cI
    cM
    cmul
    co
    #
    caddc
    co
    #
    crmy
    co
    #
    cdvds
    wbr
    #
    wb
    #
    @4
    @0
    @3
    wa
    #
    @12
    @13
    @7
    @5
    cA
    cN
    va
    cv
    #
    cM
    cmul
    co
    #
    caddc
    co
    #
    crmy
    co
    #
    cdvds
    wbr
    #
    wb
    #
    wi
    @13
    @7
    @5
    cA
    cN
    cc0
    cM
    cmul
    co
    #
    caddc
    co
    #
    crmy
    co
    #
    cdvds
    wbr
    #
    wb
    #
    wi
    @13
    @7
    @5
    cA
    cN
    vb
    cv
    #
    cM
    cmul
    co
    #
    caddc
    co
    #
    crmy
    co
    #
    cdvds
    wbr
    #
    wb
    #
    wi
    @13
    @7
    @5
    cA
    cN
    @25
    c1
    caddc
    co
    #
    cM
    cmul
    co
    #
    caddc
    co
    #
    crmy
    co
    #
    cdvds
    wbr
    #
    wb
    #
    wi
    @13
    @12
    wi
    va
    vb
    cI
    @14
    cc0
    wceq
    #
    @19
    @24
    @13
    @37
    @18
    @23
    @7
    @37
    @17
    @22
    @5
    cdvds
    @37
    @16
    @21
    cA
    crmy
    @37
    @15
    @20
    cN
    caddc
    @14
    cc0
    cM
    cmul
    oveq1
    oveq2d
    oveq2d
    breq2d
    bibi2d
    imbi2d
    va
    vb
    weq
    #
    @19
    @30
    @13
    @38
    @18
    @29
    @7
    @38
    @17
    @28
    @5
    cdvds
    @38
    @16
    @27
    cA
    crmy
    @38
    @15
    @26
    cN
    caddc
    @14
    @25
    cM
    cmul
    oveq1
    oveq2d
    oveq2d
    breq2d
    bibi2d
    imbi2d
    @14
    @31
    wceq
    #
    @19
    @36
    @13
    @39
    @18
    @35
    @7
    @39
    @17
    @34
    @5
    cdvds
    @39
    @16
    @33
    cA
    crmy
    @39
    @15
    @32
    cN
    caddc
    @14
    @31
    cM
    cmul
    oveq1
    oveq2d
    oveq2d
    breq2d
    bibi2d
    imbi2d
    @14
    cI
    wceq
    #
    @19
    @12
    @13
    @40
    @18
    @11
    @7
    @40
    @17
    @10
    @5
    cdvds
    @40
    @16
    @9
    cA
    crmy
    @40
    @15
    @8
    cN
    caddc
    @14
    cI
    cM
    cmul
    oveq1
    oveq2d
    oveq2d
    breq2d
    bibi2d
    imbi2d
    @13
    @6
    @22
    @5
    cdvds
    @13
    cN
    @21
    cA
    crmy
    @13
    @21
    cN
    cc0
    caddc
    co
    cN
    @13
    @20
    cc0
    cN
    caddc
    @13
    cM
    @1
    cM
    cc
    wcel
    @0
    @2
    cM
    zcn
    ad2antrl
    mul02d
    oveq2d
    @13
    cN
    @2
    cN
    cc
    wcel
    @0
    @1
    cN
    zcn
    ad2antll
    addid1d
    eqtr2d
    oveq2d
    breq2d
    @25
    cn0
    wcel
    #
    @13
    @30
    @36
    @41
    @13
    @30
    @36
    @41
    @13
    @30
    w3a
    @7
    @29
    @35
    @41
    @13
    @30
    simp3
    @41
    @13
    @29
    @35
    wb
    @30
    @41
    @13
    wa
    #
    @29
    @5
    cA
    @27
    cM
    caddc
    co
    #
    crmy
    co
    #
    cdvds
    wbr
    #
    @35
    @42
    @0
    @1
    @27
    cz
    wcel
    @29
    @45
    wb
    @41
    @0
    @3
    simprl
    @41
    @0
    @1
    @2
    simprrl
    #
    @42
    cN
    @26
    @41
    @0
    @1
    @2
    simprrr
    #
    @42
    @25
    cM
    @41
    @25
    cz
    wcel
    @13
    @25
    nn0z
    adantr
    @46
    zmulcld
    #
    zaddcld
    cA
    cM
    @27
    jm2.19lem2
    syl3anc
    @42
    @44
    @34
    @5
    cdvds
    @42
    @43
    @33
    cA
    crmy
    @42
    @43
    cN
    @26
    cM
    caddc
    co
    #
    caddc
    co
    @33
    @42
    cN
    @26
    cM
    @42
    cN
    @47
    zcnd
    @42
    @26
    @48
    zcnd
    @42
    cM
    @46
    zcnd
    #
    addassd
    @42
    @49
    @32
    cN
    caddc
    @42
    @32
    @26
    c1
    cM
    cmul
    co
    #
    caddc
    co
    @49
    @42
    @25
    c1
    cM
    @41
    @25
    cc
    wcel
    @13
    @25
    nn0cn
    adantr
    @42
    1cnd
    @50
    adddird
    @42
    @51
    cM
    @26
    caddc
    @42
    cM
    @50
    mulid2d
    oveq2d
    eqtr2d
    oveq2d
    eqtrd
    oveq2d
    breq2d
    bitrd
    3adant3
    bitrd
    3exp
    a2d
    nn0ind
    com12
    3impia
end
