include "crp.mm"
include "wcel.mm"
include "cv.mm"
include "ce.mm"
include "cfv.mm"
include "ccxp.mm"
include "co.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cc0.mm"
include "crli.mm"
include "wbr.mm"
include "clog.mm"
include "cr.mm"
include "c1.mm"
include "clt.mm"
include "rpre.mm"
include "reefcl.mm"
include "syl.mm"
include "efgt1.mm"
include "cxp2limlem.mm"
include "syl2anc.mm"
include "cabs.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "cle.mm"
include "cif.mm"
include "adantl.mm"
include "1re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "wb.mm"
include "a1i.mm"
include "adantr.mm"
include "maxlt.mm"
include "syl3anc.mm"
include "simprrr.mm"
include "wceq.mm"
include "reeflog.mm"
include "ad2antrl.mm"
include "breqtrrd.mm"
include "simplr.mm"
include "simprrl.mm"
include "rplogcld.mm"
include "rpred.mm"
include "eflt.mm"
include "mpbird.mm"
include "breq2.mm"
include "id.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpid.mm"
include "cmul.mm"
include "ad2antrr.mm"
include "relogefd.mm"
include "oveq2d.mm"
include "rpcnd.mm"
include "cc.mm"
include "rpcn.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "recnd.mm"
include "wne.mm"
include "efne0.mm"
include "cxpefd.mm"
include "rpne0.mm"
include "3eqtr4d.mm"
include "sylibd.mm"
include "expr.mm"
include "sylbid.mm"
include "com23.mm"
include "ralrimdva.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "ralimdv.mm"
include "simpr.mm"
include "rpefcld.mm"
include "rpcxpcld.mm"
include "rpdivcld.mm"
include "ralrimiva.mm"
include "wss.mm"
include "rpssre.mm"
include "rlim0lt.mm"
include "relogcl.mm"
include "rerpdivcld.mm"
include "3imtr4d.mm"
include "mpd.mm"

theorem cxploglim
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
  assert |- ( A e. RR+ -> ( n e. RR+ |-> ( ( log ` n ) / ( n ^c A ) ) ) ~~>r 0 )

  proof
    cA
    crp
    wcel
    #
    vm
    crp
    vm
    cv
    #
    cA
    ce
    cfv
    #
    @1
    ccxp
    co
    #
    cdiv
    co
    #
    cmpt
    cc0
    crli
    wbr
    #
    vn
    crp
    vn
    cv
    #
    clog
    cfv
    #
    @6
    cA
    ccxp
    co
    #
    cdiv
    co
    #
    cmpt
    cc0
    crli
    wbr
    #
    @0
    @2
    cr
    wcel
    #
    c1
    @2
    clt
    wbr
    @5
    @0
    cA
    cr
    wcel
    #
    @11
    cA
    rpre
    #
    cA
    reefcl
    syl
    #
    cA
    efgt1
    @2
    vm
    cxp2limlem
    syl2anc
    @0
    vz
    cv
    #
    @1
    clt
    wbr
    #
    @4
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vm
    crp
    wral
    #
    vz
    cr
    wrex
    #
    vx
    crp
    wral
    vy
    cv
    #
    @6
    clt
    wbr
    #
    @9
    cabs
    cfv
    #
    @18
    clt
    wbr
    #
    wi
    #
    vn
    crp
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    @5
    @10
    @0
    @22
    @29
    vx
    crp
    @0
    @21
    @29
    vz
    cr
    @0
    @15
    cr
    wcel
    #
    wa
    #
    c1
    @15
    ce
    cfv
    #
    cle
    wbr
    #
    @32
    c1
    cif
    #
    cr
    wcel
    #
    @21
    @34
    @6
    clt
    wbr
    #
    @26
    wi
    #
    vn
    crp
    wral
    #
    @29
    @31
    @32
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @35
    @30
    @39
    @0
    @15
    reefcl
    adantl
    #
    1re
    @33
    @32
    c1
    cr
    ifcl
    sylancl
    @31
    @21
    @37
    vn
    crp
    @31
    @6
    crp
    wcel
    #
    wa
    #
    @36
    @21
    @26
    @43
    @36
    c1
    @6
    clt
    wbr
    #
    @32
    @6
    clt
    wbr
    #
    wa
    #
    @21
    @26
    wi
    #
    @43
    @40
    @39
    @6
    cr
    wcel
    #
    @36
    @46
    wb
    @40
    @43
    1re
    a1i
    @31
    @39
    @42
    @41
    adantr
    @42
    @48
    @31
    @6
    rpre
    #
    adantl
    c1
    @32
    @6
    maxlt
    syl3anc
    @31
    @42
    @46
    @47
    @31
    @42
    @46
    wa
    #
    wa
    #
    @21
    @7
    @2
    @7
    ccxp
    co
    #
    cdiv
    co
    #
    cabs
    cfv
    #
    @18
    clt
    wbr
    #
    @26
    @51
    @21
    @15
    @7
    clt
    wbr
    #
    @55
    @51
    @56
    @32
    @7
    ce
    cfv
    #
    clt
    wbr
    #
    @51
    @32
    @6
    @57
    clt
    @31
    @42
    @44
    @45
    simprrr
    @42
    @57
    @6
    wceq
    @31
    @46
    @6
    reeflog
    ad2antrl
    breqtrrd
    @51
    @30
    @7
    cr
    wcel
    #
    @56
    @58
    wb
    @0
    @30
    @50
    simplr
    @51
    @7
    @51
    @6
    @42
    @48
    @31
    @46
    @49
    ad2antrl
    @31
    @42
    @44
    @45
    simprrl
    rplogcld
    #
    rpred
    @15
    @7
    eflt
    syl2anc
    mpbird
    @51
    @7
    crp
    wcel
    @21
    @56
    @55
    wi
    #
    wi
    @60
    @20
    @61
    vm
    @7
    crp
    @1
    @7
    wceq
    #
    @16
    @56
    @19
    @55
    @1
    @7
    @15
    clt
    breq2
    @62
    @17
    @54
    @18
    clt
    @62
    @4
    @53
    cabs
    @62
    @1
    @7
    @3
    @52
    cdiv
    @62
    id
    @1
    @7
    @2
    ccxp
    oveq2
    oveq12d
    fveq2d
    breq1d
    imbi12d
    rspcv
    syl
    mpid
    @51
    @54
    @25
    @18
    clt
    @51
    @53
    @9
    cabs
    @51
    @52
    @8
    @7
    cdiv
    @51
    @7
    @2
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    cA
    @7
    cmul
    co
    #
    ce
    cfv
    @52
    @8
    @51
    @64
    @65
    ce
    @51
    @64
    @7
    cA
    cmul
    co
    @65
    @51
    @63
    cA
    @7
    cmul
    @51
    cA
    @0
    @12
    @30
    @50
    @13
    ad2antrr
    relogefd
    oveq2d
    @51
    @7
    cA
    @51
    @7
    @60
    rpcnd
    #
    @0
    cA
    cc
    wcel
    #
    @30
    @50
    cA
    rpcn
    ad2antrr
    #
    mulcomd
    eqtrd
    fveq2d
    @51
    @2
    @7
    @51
    @2
    @0
    @11
    @30
    @50
    @14
    ad2antrr
    recnd
    @51
    @67
    @2
    cc0
    wne
    @68
    cA
    efne0
    syl
    @66
    cxpefd
    @51
    @6
    cA
    @42
    @6
    cc
    wcel
    @31
    @46
    @6
    rpcn
    ad2antrl
    @42
    @6
    cc0
    wne
    @31
    @46
    @6
    rpne0
    ad2antrl
    @68
    cxpefd
    3eqtr4d
    oveq2d
    fveq2d
    breq1d
    sylibd
    expr
    sylbid
    com23
    ralrimdva
    @28
    @38
    vy
    @34
    cr
    @23
    @34
    wceq
    #
    @27
    @37
    vn
    crp
    @69
    @24
    @36
    @26
    @23
    @34
    @6
    clt
    breq1
    imbi1d
    ralbidv
    rspcev
    syl6an
    rexlimdva
    ralimdv
    @0
    vx
    vz
    vm
    crp
    @4
    @0
    @4
    cc
    wcel
    vm
    crp
    @0
    @1
    crp
    wcel
    #
    wa
    #
    @4
    @71
    @1
    @3
    @0
    @70
    simpr
    @71
    @2
    @1
    @71
    cA
    @0
    @12
    @70
    @13
    adantr
    rpefcld
    @70
    @1
    cr
    wcel
    @0
    @1
    rpre
    adantl
    rpcxpcld
    rpdivcld
    rpcnd
    ralrimiva
    crp
    cr
    wss
    @0
    rpssre
    a1i
    #
    rlim0lt
    @0
    vx
    vy
    vn
    crp
    @9
    @0
    @9
    cc
    wcel
    vn
    crp
    @0
    @42
    wa
    #
    @9
    @73
    @7
    @8
    @42
    @59
    @0
    @6
    relogcl
    adantl
    @73
    @6
    cA
    @0
    @42
    simpr
    @0
    @12
    @42
    @13
    adantr
    rpcxpcld
    rerpdivcld
    recnd
    ralrimiva
    @72
    rlim0lt
    3imtr4d
    mpd
end
