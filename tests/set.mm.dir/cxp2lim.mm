include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "crp.mm"
include "cv.mm"
include "ccxp.mm"
include "co.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cc0.mm"
include "crli.mm"
include "cpnf.mm"
include "cico.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "cle.mm"
include "wa.mm"
include "wb.mm"
include "1re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "simplbi.mm"
include "0red.mm"
include "a1i.mm"
include "0lt1.mm"
include "simprbi.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "ssriv.mm"
include "resmpt.mm"
include "cif.mm"
include "rpre.mm"
include "adantl.mm"
include "rpge0.mm"
include "simpl2.mm"
include "simpl3.mm"
include "lttrd.mm"
include "rpcxpcld.mm"
include "simp1.mm"
include "ifcl.mm"
include "sylancl.mm"
include "max1.mm"
include "sylancr.mm"
include "rprecred.mm"
include "adantr.mm"
include "cc.mm"
include "recnd.mm"
include "divcxpd.mm"
include "cmul.mm"
include "rpne0d.mm"
include "recid2d.mm"
include "oveq2d.mm"
include "cxpmuld.mm"
include "rpcnd.mm"
include "cxp1d.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "ovexd.mm"
include "mulcomd.mm"
include "simp2.mm"
include "simp3.mm"
include "rpred.mm"
include "1cxpd.mm"
include "0le1.mm"
include "rpge0d.mm"
include "rpreccld.mm"
include "cxplt2d.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "cxp2limlem.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "rlimcxp.mm"
include "rlimres2.mm"
include "simpr.mm"
include "rpdivcld.mm"
include "sylan2.mm"
include "simpl1.mm"
include "max2.mm"
include "cxplead.mm"
include "lediv1dd.mm"
include "adantrr.mm"
include "rlimsqz2.mm"
include "syl5eqbr.mm"
include "eqid.mm"
include "fmptd.mm"
include "rpssre.mm"
include "rlimresb.mm"
include "mpbird.mm"

theorem cxp2lim
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint A n
  disjoint B n
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( ( A e. RR /\ B e. RR /\ 1 < B ) -> ( n e. RR+ |-> ( ( n ^c A ) / ( B ^c n ) ) ) ~~>r 0 )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    c1
    cB
    clt
    wbr
    #
    w3a
    #
    vn
    crp
    vn
    cv
    #
    cA
    ccxp
    co
    #
    cB
    @4
    ccxp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cc0
    crli
    wbr
    @8
    c1
    cpnf
    cico
    co
    #
    cres
    #
    cc0
    crli
    wbr
    @3
    @10
    vn
    @9
    @7
    cmpt
    #
    cc0
    crli
    @9
    crp
    wss
    #
    @10
    @11
    wceq
    vn
    @9
    crp
    @4
    @9
    wcel
    #
    @4
    @13
    @4
    cr
    wcel
    #
    c1
    @4
    cle
    wbr
    #
    c1
    cr
    wcel
    #
    @13
    @14
    @15
    wa
    wb
    1re
    c1
    @4
    elicopnf
    ax-mp
    #
    simplbi
    #
    @13
    cc0
    c1
    @4
    @13
    0red
    @16
    @13
    1re
    a1i
    @18
    cc0
    c1
    clt
    wbr
    #
    @13
    0lt1
    a1i
    @13
    @14
    @15
    @17
    simprbi
    #
    ltletrd
    elrpd
    #
    ssriv
    #
    vn
    crp
    @9
    @7
    resmpt
    ax-mp
    @3
    vn
    @9
    @4
    c1
    cA
    cle
    wbr
    #
    cA
    c1
    cif
    #
    ccxp
    co
    #
    @6
    cdiv
    co
    #
    @7
    cc0
    cc0
    @3
    0red
    #
    @27
    @3
    vn
    @9
    crp
    @26
    cc0
    @12
    @3
    @22
    a1i
    @3
    vn
    crp
    @4
    @6
    c1
    @24
    cdiv
    co
    #
    ccxp
    co
    #
    cdiv
    co
    #
    @24
    ccxp
    co
    #
    cmpt
    vn
    crp
    @26
    cmpt
    cc0
    crli
    @3
    vn
    crp
    @31
    @26
    @3
    @4
    crp
    wcel
    #
    wa
    #
    @31
    @25
    @29
    @24
    ccxp
    co
    #
    cdiv
    co
    @26
    @33
    @4
    @29
    @24
    @32
    @14
    @3
    @4
    rpre
    adantl
    #
    @32
    cc0
    @4
    cle
    wbr
    #
    @3
    @4
    rpge0
    adantl
    @33
    @6
    @28
    @33
    cB
    @4
    @33
    cB
    @0
    @1
    @2
    @32
    simpl2
    #
    @33
    cc0
    c1
    cB
    @33
    0red
    @16
    @33
    1re
    a1i
    @37
    @19
    @33
    0lt1
    a1i
    @0
    @1
    @2
    @32
    simpl3
    lttrd
    elrpd
    #
    @35
    rpcxpcld
    #
    @3
    @28
    cr
    wcel
    @32
    @3
    @24
    @3
    @24
    @3
    @0
    @16
    @24
    cr
    wcel
    #
    @0
    @1
    @2
    simp1
    #
    1re
    @23
    cA
    c1
    cr
    ifcl
    sylancl
    #
    @3
    cc0
    c1
    @24
    @27
    @16
    @3
    1re
    a1i
    #
    @42
    @19
    @3
    0lt1
    a1i
    #
    @3
    @16
    @0
    c1
    @24
    cle
    wbr
    1re
    @41
    c1
    cA
    max1
    sylancr
    ltletrd
    elrpd
    #
    rprecred
    #
    adantr
    #
    rpcxpcld
    @3
    @24
    cc
    wcel
    @32
    @3
    @24
    @42
    recnd
    adantr
    #
    divcxpd
    @33
    @34
    @6
    @25
    cdiv
    @33
    @6
    @28
    @24
    cmul
    co
    #
    ccxp
    co
    @6
    c1
    ccxp
    co
    @34
    @6
    @33
    @49
    c1
    @6
    ccxp
    @33
    @24
    @48
    @33
    @24
    @3
    @24
    crp
    wcel
    @32
    @45
    adantr
    rpne0d
    recid2d
    oveq2d
    @33
    @6
    @28
    @24
    @39
    @47
    @48
    cxpmuld
    @33
    @6
    @33
    @6
    @39
    rpcnd
    cxp1d
    3eqtr3d
    oveq2d
    eqtrd
    mpteq2dva
    @3
    crp
    @30
    @24
    vn
    cvv
    @33
    @4
    @29
    cdiv
    ovexd
    @3
    vn
    crp
    @30
    cmpt
    vn
    crp
    @4
    cB
    @28
    ccxp
    co
    #
    @4
    ccxp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cc0
    crli
    @3
    vn
    crp
    @30
    @52
    @33
    @29
    @51
    @4
    cdiv
    @33
    cB
    @4
    @28
    cmul
    co
    #
    ccxp
    co
    cB
    @28
    @4
    cmul
    co
    #
    ccxp
    co
    @29
    @51
    @33
    @54
    @55
    cB
    ccxp
    @33
    @4
    @28
    @33
    @4
    @35
    recnd
    #
    @3
    @28
    cc
    wcel
    @32
    @3
    @28
    @46
    recnd
    #
    adantr
    #
    mulcomd
    oveq2d
    @33
    cB
    @4
    @28
    @38
    @35
    @58
    cxpmuld
    @33
    cB
    @28
    @4
    @38
    @47
    @56
    cxpmuld
    3eqtr3d
    oveq2d
    mpteq2dva
    @3
    @50
    cr
    wcel
    c1
    @50
    clt
    wbr
    @53
    cc0
    crli
    wbr
    @3
    @50
    @3
    cB
    @28
    @3
    cB
    @0
    @1
    @2
    simp2
    #
    @3
    cc0
    c1
    cB
    @27
    @43
    @59
    @44
    @0
    @1
    @2
    simp3
    #
    lttrd
    elrpd
    #
    @46
    rpcxpcld
    rpred
    @3
    c1
    @28
    ccxp
    co
    #
    c1
    @50
    clt
    @3
    @28
    @57
    1cxpd
    @3
    @2
    @62
    @50
    clt
    wbr
    @60
    @3
    c1
    cB
    @28
    @43
    cc0
    c1
    cle
    wbr
    @3
    0le1
    a1i
    @59
    @3
    cB
    @61
    rpge0d
    @3
    @24
    @45
    rpreccld
    cxplt2d
    mpbid
    eqbrtrrd
    @50
    vn
    cxp2limlem
    syl2anc
    eqbrtrd
    @45
    rlimcxp
    eqbrtrrd
    rlimres2
    @13
    @3
    @32
    @26
    cr
    wcel
    @21
    @33
    @26
    @33
    @25
    @6
    @33
    @4
    @24
    @3
    @32
    simpr
    #
    @3
    @40
    @32
    @42
    adantr
    rpcxpcld
    #
    @39
    rpdivcld
    rpred
    sylan2
    @3
    @13
    wa
    #
    @7
    @13
    @3
    @32
    @7
    crp
    wcel
    @21
    @33
    @5
    @6
    @33
    @4
    cA
    @63
    @0
    @1
    @2
    @32
    simpl1
    rpcxpcld
    #
    @39
    rpdivcld
    #
    sylan2
    #
    rpred
    @3
    @13
    @7
    @26
    cle
    wbr
    @36
    @65
    @5
    @25
    @6
    @65
    @5
    @13
    @3
    @32
    @5
    crp
    wcel
    @21
    @66
    sylan2
    rpred
    @65
    @25
    @13
    @3
    @32
    @25
    crp
    wcel
    @21
    @64
    sylan2
    rpred
    @13
    @3
    @32
    @6
    crp
    wcel
    @21
    @39
    sylan2
    @65
    @4
    cA
    @24
    @13
    @14
    @3
    @18
    adantl
    @13
    @15
    @3
    @20
    adantl
    @0
    @1
    @2
    @13
    simpl1
    #
    @3
    @40
    @13
    @42
    adantr
    @65
    @16
    @0
    cA
    @24
    cle
    wbr
    1re
    @69
    c1
    cA
    max2
    sylancr
    cxplead
    lediv1dd
    adantrr
    @3
    @13
    cc0
    @7
    cle
    wbr
    @36
    @65
    @7
    @68
    rpge0d
    adantrr
    rlimsqz2
    syl5eqbr
    @3
    crp
    c1
    cc0
    @8
    @3
    vn
    crp
    @7
    cc
    @8
    @33
    @7
    @67
    rpcnd
    @8
    eqid
    fmptd
    crp
    cr
    wss
    @3
    rpssre
    a1i
    @43
    rlimresb
    mpbird
end
