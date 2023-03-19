include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cpr.mm"
include "cv.mm"
include "cmin.mm"
include "cmul.mm"
include "wa.mm"
include "wrex.mm"
include "wo.mm"
include "cgcd.mm"
include "cdiv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "divgcdodd.mm"
include "3adant3.mm"
include "adantr.mm"
include "pythagtriplem19.mm"
include "3expia.mm"
include "simp12.mm"
include "simp11.mm"
include "simp13.mm"
include "cc.mm"
include "nnsqcl.mm"
include "nncnd.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "addcomd.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "cz.mm"
include "nnz.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "notbid.mm"
include "biimp3a.mm"
include "syl311anc.mm"
include "orim12d.mm"
include "mpd.mm"
include "wb.mm"
include "cvv.mm"
include "ovex.mm"
include "preq12bg.mm"
include "mpanr12.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "andir.mm"
include "df-3an.mm"
include "orbi12i.mm"
include "3ancoma.mm"
include "orbi2i.mm"
include "3bitr2i.mm"
include "rexbii.mm"
include "2rexbii.mm"
include "r19.43.mm"
include "bitri.mm"
include "syl6bb.mm"
include "mpbird.mm"
include "ex.mm"
include "wi.mm"
include "pythagtriplem2.mm"
include "impbid.mm"

theorem pythagtrip
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n

  disjoint A k
  disjoint A m
  disjoint A n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint C k
  disjoint C m
  disjoint C n
  assert |- ( ( A e. NN /\ B e. NN /\ C e. NN ) -> ( ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) <-> E. n e. NN E. m e. NN E. k e. NN ( { A , B } = { ( k x. ( ( m ^ 2 ) - ( n ^ 2 ) ) ) , ( k x. ( 2 x. ( m x. n ) ) ) } /\ C = ( k x. ( ( m ^ 2 ) + ( n ^ 2 ) ) ) ) ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cC
    cn
    wcel
    #
    w3a
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    cC
    c2
    cexp
    co
    #
    wceq
    #
    cA
    cB
    cpr
    vk
    cv
    #
    vm
    cv
    #
    c2
    cexp
    co
    #
    vn
    cv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    @9
    c2
    @10
    @12
    cmul
    co
    cmul
    co
    #
    cmul
    co
    #
    cpr
    wceq
    #
    cC
    @9
    @11
    @13
    caddc
    co
    cmul
    co
    wceq
    #
    wa
    #
    vk
    cn
    wrex
    #
    vm
    cn
    wrex
    vn
    cn
    wrex
    #
    @3
    @8
    @22
    @3
    @8
    wa
    #
    @22
    cA
    @15
    wceq
    #
    cB
    @17
    wceq
    #
    @19
    w3a
    #
    vk
    cn
    wrex
    #
    vm
    cn
    wrex
    #
    vn
    cn
    wrex
    #
    cB
    @15
    wceq
    #
    cA
    @17
    wceq
    #
    @19
    w3a
    #
    vk
    cn
    wrex
    #
    vm
    cn
    wrex
    #
    vn
    cn
    wrex
    #
    wo
    #
    @23
    c2
    cA
    cA
    cB
    cgcd
    co
    #
    cdiv
    co
    cdvds
    wbr
    wn
    #
    c2
    cB
    @37
    cdiv
    co
    #
    cdvds
    wbr
    #
    wn
    #
    wo
    #
    @36
    @3
    @42
    @8
    @0
    @1
    @42
    @2
    cA
    cB
    divgcdodd
    3adant3
    adantr
    @23
    @38
    @29
    @41
    @35
    @3
    @8
    @38
    @29
    cA
    cB
    cC
    vk
    vm
    vn
    pythagtriplem19
    3expia
    @3
    @8
    @41
    @35
    @3
    @8
    @41
    w3a
    @1
    @0
    @2
    @5
    @4
    caddc
    co
    #
    @7
    wceq
    #
    c2
    cB
    cB
    cA
    cgcd
    co
    #
    cdiv
    co
    #
    cdvds
    wbr
    #
    wn
    #
    @35
    @0
    @1
    @2
    @8
    @41
    simp12
    @0
    @1
    @2
    @8
    @41
    simp11
    @0
    @1
    @2
    @8
    @41
    simp13
    @3
    @8
    @44
    @41
    @3
    @8
    @44
    @3
    @6
    @43
    @7
    @3
    @4
    @5
    @0
    @1
    @4
    cc
    wcel
    @2
    @0
    @4
    cA
    nnsqcl
    nncnd
    3ad2ant1
    @1
    @0
    @5
    cc
    wcel
    @2
    @1
    @5
    cB
    nnsqcl
    nncnd
    3ad2ant2
    addcomd
    eqeq1d
    biimpa
    3adant3
    @3
    @8
    @41
    @48
    @23
    @40
    @47
    @23
    @39
    @46
    c2
    cdvds
    @23
    @37
    @45
    cB
    cdiv
    @23
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @37
    @45
    wceq
    @3
    @49
    @8
    @0
    @1
    @49
    @2
    cA
    nnz
    3ad2ant1
    adantr
    @3
    @50
    @8
    @1
    @0
    @50
    @2
    cB
    nnz
    3ad2ant2
    adantr
    cA
    cB
    gcdcom
    syl2anc
    oveq2d
    breq2d
    notbid
    biimp3a
    cB
    cA
    cC
    vk
    vm
    vn
    pythagtriplem19
    syl311anc
    3expia
    orim12d
    mpd
    @3
    @22
    @36
    wb
    #
    @8
    @0
    @1
    @51
    @2
    @0
    @1
    wa
    #
    @22
    @24
    @25
    wa
    #
    @31
    @30
    wa
    #
    wo
    #
    @19
    wa
    #
    vk
    cn
    wrex
    #
    vm
    cn
    wrex
    vn
    cn
    wrex
    #
    @36
    @52
    @21
    @57
    vn
    vm
    cn
    cn
    @52
    @20
    @56
    vk
    cn
    @52
    @18
    @55
    @19
    @52
    @15
    cvv
    wcel
    @17
    cvv
    wcel
    @18
    @55
    wb
    @9
    @14
    cmul
    ovex
    @9
    @16
    cmul
    ovex
    cA
    cB
    @15
    @17
    cn
    cn
    cvv
    cvv
    preq12bg
    mpanr12
    anbi1d
    rexbidv
    2rexbidv
    @58
    @26
    @32
    wo
    #
    vk
    cn
    wrex
    #
    vm
    cn
    wrex
    vn
    cn
    wrex
    #
    @36
    @57
    @60
    vn
    vm
    cn
    cn
    @56
    @59
    vk
    cn
    @56
    @53
    @19
    wa
    #
    @54
    @19
    wa
    #
    wo
    @26
    @31
    @30
    @19
    w3a
    #
    wo
    @59
    @53
    @54
    @19
    andir
    @26
    @62
    @64
    @63
    @24
    @25
    @19
    df-3an
    @31
    @30
    @19
    df-3an
    orbi12i
    @64
    @32
    @26
    @31
    @30
    @19
    3ancoma
    orbi2i
    3bitr2i
    rexbii
    2rexbii
    @61
    @27
    @33
    wo
    #
    vm
    cn
    wrex
    #
    vn
    cn
    wrex
    #
    @36
    @60
    @65
    vn
    vm
    cn
    cn
    @26
    @32
    vk
    cn
    r19.43
    2rexbii
    @67
    @28
    @34
    wo
    #
    vn
    cn
    wrex
    @36
    @66
    @68
    vn
    cn
    @27
    @33
    vm
    cn
    r19.43
    rexbii
    @28
    @34
    vn
    cn
    r19.43
    bitri
    bitri
    bitri
    syl6bb
    3adant3
    adantr
    mpbird
    ex
    @0
    @1
    @22
    @8
    wi
    @2
    cA
    cB
    cC
    vk
    vm
    vn
    pythagtriplem2
    3adant3
    impbid
end
