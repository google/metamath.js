include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "crp.mm"
include "c2.mm"
include "clog.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cv.mm"
include "ccxp.mm"
include "cc0.mm"
include "0red.mm"
include "cc.mm"
include "cmpt.mm"
include "crli.mm"
include "2rp.mm"
include "cz.mm"
include "rplogcl.mm"
include "2z.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "rpdivcl.mm"
include "sylancr.mm"
include "rpcnd.mm"
include "divrcnv.mm"
include "syl.mm"
include "rpred.mm"
include "rerpdivcl.mm"
include "sylan.mm"
include "simpr.mm"
include "simpl.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "lttrd.mm"
include "elrpd.mm"
include "rpre.mm"
include "rpcxpcl.mm"
include "syl2an.mm"
include "rpdivcld.mm"
include "cle.mm"
include "cmul.mm"
include "ce.mm"
include "caddc.mm"
include "adantr.mm"
include "rpmulcld.mm"
include "resqcld.mm"
include "rehalfcld.mm"
include "1rp.mm"
include "rpaddcl.mm"
include "readdcld.mm"
include "reefcld.mm"
include "ltaddrp2d.mm"
include "efgt1p2.mm"
include "adantl.mm"
include "recnd.mm"
include "sqcld.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "rpne0d.mm"
include "divdiv2d.mm"
include "sqmuld.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "cxpefd.mm"
include "3brtr4d.mm"
include "ltdiv2d.mm"
include "mpbid.mm"
include "sqvald.mm"
include "oveq2d.mm"
include "rpne0.mm"
include "divcan5d.mm"
include "3eqtrd.mm"
include "breqtrd.mm"
include "ltled.mm"
include "adantrr.mm"
include "rpge0d.mm"
include "rlimsqz2.mm"

theorem cxp2limlem
  let cA: class A
  let vn: setvar n
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint A n
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
  disjoint B n
  assert |- ( ( A e. RR /\ 1 < A ) -> ( n e. RR+ |-> ( n / ( A ^c n ) ) ) ~~>r 0 )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    wa
    #
    vn
    crp
    c2
    cA
    clog
    cfv
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    vn
    cv
    #
    cdiv
    co
    #
    @6
    cA
    @6
    ccxp
    co
    #
    cdiv
    co
    #
    cc0
    cc0
    @2
    0red
    #
    @10
    @2
    @5
    cc
    wcel
    #
    vn
    crp
    @7
    cmpt
    cc0
    crli
    wbr
    @2
    @5
    @2
    c2
    crp
    wcel
    @4
    crp
    wcel
    #
    @5
    crp
    wcel
    #
    2rp
    @2
    @3
    crp
    wcel
    #
    c2
    cz
    wcel
    #
    @12
    cA
    rplogcl
    #
    2z
    @3
    c2
    rpexpcl
    sylancl
    #
    c2
    @4
    rpdivcl
    sylancr
    #
    rpcnd
    #
    @5
    vn
    divrcnv
    syl
    @2
    @5
    cr
    wcel
    @6
    crp
    wcel
    #
    @7
    cr
    wcel
    @2
    @5
    @18
    rpred
    @5
    @6
    rerpdivcl
    sylan
    #
    @2
    @20
    wa
    #
    @9
    @22
    @6
    @8
    @2
    @20
    simpr
    #
    @2
    cA
    crp
    wcel
    #
    @6
    cr
    wcel
    #
    @8
    crp
    wcel
    @20
    @2
    cA
    @0
    @1
    simpl
    #
    @2
    cc0
    c1
    cA
    @10
    @2
    1red
    @26
    cc0
    c1
    clt
    wbr
    @2
    0lt1
    a1i
    @0
    @1
    simpr
    lttrd
    elrpd
    #
    @6
    rpre
    #
    cA
    @6
    rpcxpcl
    syl2an
    #
    rpdivcld
    #
    rpred
    #
    @2
    @20
    @9
    @7
    cle
    wbr
    cc0
    @6
    cle
    wbr
    #
    @22
    @9
    @7
    @31
    @21
    @22
    @9
    @6
    @6
    c2
    cexp
    co
    #
    @5
    cdiv
    co
    #
    cdiv
    co
    #
    @7
    clt
    @22
    @34
    @8
    clt
    wbr
    @9
    @35
    clt
    wbr
    @22
    @6
    @3
    cmul
    co
    #
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    @36
    ce
    cfv
    #
    @34
    @8
    clt
    @22
    @38
    c1
    @36
    caddc
    co
    #
    @38
    caddc
    co
    #
    @39
    @22
    @37
    @22
    @36
    @22
    @36
    @22
    @6
    @3
    @23
    @2
    @14
    @20
    @16
    adantr
    rpmulcld
    #
    rpred
    #
    resqcld
    rehalfcld
    #
    @22
    @40
    @38
    @22
    @40
    @22
    c1
    crp
    wcel
    @36
    crp
    wcel
    #
    @40
    crp
    wcel
    1rp
    @42
    c1
    @36
    rpaddcl
    sylancr
    #
    rpred
    @44
    readdcld
    @22
    @36
    @43
    reefcld
    @22
    @38
    @40
    @44
    @46
    ltaddrp2d
    @22
    @45
    @41
    @39
    clt
    wbr
    @42
    @36
    efgt1p2
    syl
    lttrd
    @22
    @34
    @33
    @4
    cmul
    co
    #
    c2
    cdiv
    co
    @38
    @22
    @33
    c2
    @4
    @22
    @6
    @22
    @6
    @20
    @25
    @2
    @28
    adantl
    recnd
    #
    sqcld
    #
    @22
    2cnd
    @22
    @4
    @2
    @12
    @20
    @17
    adantr
    #
    rpcnd
    c2
    cc0
    wne
    @22
    2ne0
    a1i
    @22
    @4
    @50
    rpne0d
    divdiv2d
    @22
    @37
    @47
    c2
    cdiv
    @22
    @6
    @3
    @48
    @2
    @3
    cc
    wcel
    @20
    @2
    @3
    @16
    rpcnd
    adantr
    sqmuld
    oveq1d
    eqtr4d
    @22
    cA
    @6
    @2
    cA
    cc
    wcel
    @20
    @2
    cA
    @26
    recnd
    adantr
    @22
    cA
    @2
    @24
    @20
    @27
    adantr
    rpne0d
    @48
    cxpefd
    3brtr4d
    @22
    @34
    @8
    @6
    @22
    @33
    @5
    @22
    @20
    @15
    @33
    crp
    wcel
    @23
    2z
    @6
    c2
    rpexpcl
    sylancl
    #
    @2
    @13
    @20
    @18
    adantr
    #
    rpdivcld
    @29
    @23
    ltdiv2d
    mpbid
    @22
    @35
    @6
    @5
    cmul
    co
    #
    @33
    cdiv
    co
    @53
    @6
    @6
    cmul
    co
    #
    cdiv
    co
    @7
    @22
    @6
    @33
    @5
    @48
    @49
    @2
    @11
    @20
    @19
    adantr
    #
    @22
    @33
    @51
    rpne0d
    @22
    @5
    @52
    rpne0d
    divdiv2d
    @22
    @33
    @54
    @53
    cdiv
    @22
    @6
    @48
    sqvald
    oveq2d
    @22
    @5
    @6
    @6
    @55
    @48
    @48
    @20
    @6
    cc0
    wne
    @2
    @6
    rpne0
    adantl
    #
    @56
    divcan5d
    3eqtrd
    breqtrd
    ltled
    adantrr
    @2
    @20
    cc0
    @9
    cle
    wbr
    @32
    @22
    @9
    @30
    rpge0d
    adantrr
    rlimsqz2
end
