include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "wo.mm"
include "cc0.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "orbi12d.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "oveq1.mm"
include "wcel.mm"
include "0z.mm"
include "2cn.mm"
include "mul02i.mm"
include "rspcev.mm"
include "mp2an.mm"
include "olci.mm"
include "cn0.mm"
include "orcom.mm"
include "wa.mm"
include "cc.mm"
include "zcn.mm"
include "mulcom.mm"
include "sylancl.mm"
include "adantl.mm"
include "wi.mm"
include "eqid.mm"
include "mpan2.mm"
include "eqeq2d.mm"
include "syl5ibcom.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "peano2z.mm"
include "mulid2i.mm"
include "a1i.mm"
include "oveq12d.mm"
include "df-2.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "ax-1cn.mm"
include "adddir.mm"
include "mp3an23.mm"
include "mulcl.mm"
include "mpan.mm"
include "addass.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "syl2anc.mm"
include "orim12d.mm"
include "syl5bi.mm"
include "nn0ind.mm"

theorem odd2np1lem
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y

  disjoint N k
  disjoint N n
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint k m
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint N j
  disjoint n x
  disjoint n y
  disjoint k x
  assert |- ( N e. NN0 -> ( E. n e. ZZ ( ( 2 x. n ) + 1 ) = N \/ E. k e. ZZ ( k x. 2 ) = N ) )

  proof
    c2
    vn
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    vj
    cv
    #
    wceq
    #
    vn
    cz
    wrex
    #
    vk
    cv
    #
    c2
    cmul
    co
    #
    @3
    wceq
    #
    vk
    cz
    wrex
    #
    wo
    @2
    cc0
    wceq
    #
    vn
    cz
    wrex
    #
    @7
    cc0
    wceq
    #
    vk
    cz
    wrex
    #
    wo
    c2
    vx
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    vm
    cv
    #
    wceq
    #
    vx
    cz
    wrex
    #
    vy
    cv
    #
    c2
    cmul
    co
    #
    @17
    wceq
    #
    vy
    cz
    wrex
    #
    wo
    #
    @2
    @17
    c1
    caddc
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    @7
    @25
    wceq
    #
    vk
    cz
    wrex
    #
    wo
    #
    @2
    cN
    wceq
    #
    vn
    cz
    wrex
    #
    @7
    cN
    wceq
    #
    vk
    cz
    wrex
    #
    wo
    vj
    vm
    cN
    @3
    cc0
    wceq
    #
    @5
    @11
    @9
    @13
    @35
    @4
    @10
    vn
    cz
    @3
    cc0
    @2
    eqeq2
    rexbidv
    @35
    @8
    @12
    vk
    cz
    @3
    cc0
    @7
    eqeq2
    rexbidv
    orbi12d
    vj
    vm
    weq
    #
    @5
    @19
    @9
    @23
    @36
    @5
    @2
    @17
    wceq
    #
    vn
    cz
    wrex
    @19
    @36
    @4
    @37
    vn
    cz
    @3
    @17
    @2
    eqeq2
    rexbidv
    @37
    @18
    vn
    vx
    cz
    vn
    vx
    weq
    #
    @2
    @16
    @17
    @38
    @1
    @15
    c1
    caddc
    @0
    @14
    c2
    cmul
    oveq2
    oveq1d
    eqeq1d
    cbvrexv
    syl6bb
    @36
    @9
    @7
    @17
    wceq
    #
    vk
    cz
    wrex
    @23
    @36
    @8
    @39
    vk
    cz
    @3
    @17
    @7
    eqeq2
    rexbidv
    @39
    @22
    vk
    vy
    cz
    vk
    vy
    weq
    @7
    @21
    @17
    @6
    @20
    c2
    cmul
    oveq1
    eqeq1d
    cbvrexv
    syl6bb
    orbi12d
    @3
    @25
    wceq
    #
    @5
    @27
    @9
    @29
    @40
    @4
    @26
    vn
    cz
    @3
    @25
    @2
    eqeq2
    rexbidv
    @40
    @8
    @28
    vk
    cz
    @3
    @25
    @7
    eqeq2
    rexbidv
    orbi12d
    @3
    cN
    wceq
    #
    @5
    @32
    @9
    @34
    @41
    @4
    @31
    vn
    cz
    @3
    cN
    @2
    eqeq2
    rexbidv
    @41
    @8
    @33
    vk
    cz
    @3
    cN
    @7
    eqeq2
    rexbidv
    orbi12d
    @13
    @11
    cc0
    cz
    wcel
    cc0
    c2
    cmul
    co
    #
    cc0
    wceq
    #
    @13
    0z
    c2
    2cn
    mul02i
    @12
    @43
    vk
    cc0
    cz
    @6
    cc0
    wceq
    @7
    @42
    cc0
    @6
    cc0
    c2
    cmul
    oveq1
    eqeq1d
    rspcev
    mp2an
    olci
    @24
    @23
    @19
    wo
    @17
    cn0
    wcel
    #
    @30
    @19
    @23
    orcom
    @44
    @23
    @27
    @19
    @29
    @44
    @22
    @27
    vy
    cz
    @44
    @20
    cz
    wcel
    #
    wa
    #
    @22
    c2
    @20
    cmul
    co
    #
    @17
    wceq
    #
    @27
    @46
    @21
    @47
    @17
    @45
    @21
    @47
    wceq
    #
    @44
    @45
    @20
    cc
    wcel
    c2
    cc
    wcel
    #
    @49
    @20
    zcn
    2cn
    @20
    c2
    mulcom
    sylancl
    adantl
    eqeq1d
    @45
    @48
    @27
    wi
    @44
    @45
    @2
    @47
    c1
    caddc
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    @48
    @27
    @45
    @51
    @51
    wceq
    #
    @53
    @51
    eqid
    @52
    @54
    vn
    @20
    cz
    vn
    vy
    weq
    #
    @2
    @51
    @51
    @55
    @1
    @47
    c1
    caddc
    @0
    @20
    c2
    cmul
    oveq2
    oveq1d
    eqeq1d
    rspcev
    mpan2
    @48
    @52
    @26
    vn
    cz
    @48
    @51
    @25
    @2
    @47
    @17
    c1
    caddc
    oveq1
    eqeq2d
    rexbidv
    syl5ibcom
    adantl
    sylbid
    rexlimdva
    @44
    @18
    @29
    vx
    cz
    @44
    @14
    cz
    wcel
    #
    wa
    #
    @7
    @16
    c1
    caddc
    co
    #
    wceq
    #
    vk
    cz
    wrex
    #
    @18
    @29
    @57
    @14
    c1
    caddc
    co
    #
    cz
    wcel
    #
    @61
    c2
    cmul
    co
    #
    @58
    wceq
    #
    @60
    @56
    @62
    @44
    @14
    peano2z
    adantl
    @56
    @64
    @44
    @56
    @14
    cc
    wcel
    #
    @64
    @14
    zcn
    @65
    @14
    c2
    cmul
    co
    #
    c1
    c2
    cmul
    co
    #
    caddc
    co
    #
    @15
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @63
    @58
    @65
    @68
    @15
    c2
    caddc
    co
    @70
    @65
    @66
    @15
    @67
    c2
    caddc
    @65
    @50
    @66
    @15
    wceq
    2cn
    @14
    c2
    mulcom
    mpan2
    @67
    c2
    wceq
    @65
    c2
    2cn
    mulid2i
    a1i
    oveq12d
    c2
    @69
    @15
    caddc
    df-2
    oveq2i
    syl6eq
    @65
    c1
    cc
    wcel
    #
    @50
    @63
    @68
    wceq
    ax-1cn
    2cn
    @14
    c1
    c2
    adddir
    mp3an23
    @65
    @15
    cc
    wcel
    #
    @58
    @70
    wceq
    #
    @50
    @65
    @72
    2cn
    c2
    @14
    mulcl
    mpan
    @72
    @71
    @71
    @73
    ax-1cn
    ax-1cn
    @15
    c1
    c1
    addass
    mp3an23
    syl
    3eqtr4d
    syl
    adantl
    @59
    @64
    vk
    @61
    cz
    @6
    @61
    wceq
    @7
    @63
    @58
    @6
    @61
    c2
    cmul
    oveq1
    eqeq1d
    rspcev
    syl2anc
    @18
    @59
    @28
    vk
    cz
    @18
    @58
    @25
    @7
    @16
    @17
    c1
    caddc
    oveq1
    eqeq2d
    rexbidv
    syl5ibcom
    rexlimdva
    orim12d
    syl5bi
    nn0ind
end
