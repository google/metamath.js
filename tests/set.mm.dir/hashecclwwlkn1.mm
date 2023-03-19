include "cqs.mm"
include "wcel.mm"
include "cprime.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "cv.mm"
include "ccsh.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "crab.mm"
include "eclclwwlkn1.mm"
include "wa.mm"
include "cvtx.mm"
include "cword.mm"
include "cclwwlkn.mm"
include "rabeq.mm"
include "mp1i.mm"
include "cn0.mm"
include "prmnn.mm"
include "nnnn0d.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "clwwlknscsh.mm"
include "syl2an.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "cfzo.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cn.mm"
include "simpll.mm"
include "elnnne0.mm"
include "wb.mm"
include "eqeq1.mm"
include "eqcoms.mm"
include "hasheq0.mm"
include "sylan9bbr.mm"
include "necon3bid.mm"
include "biimpcd.mm"
include "simplbiim.mm"
include "impcom.mm"
include "simplr.mm"
include "eqcomd.mm"
include "3jca.mm"
include "ex.mm"
include "eqid.mm"
include "clwwlknbp.mm"
include "syl11.mm"
include "syl5bi.mm"
include "syl.mm"
include "imp.mm"
include "scshwfzeqfzo.mm"
include "oveq2.mm"
include "cbvrexv.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "cbvrabv.mm"
include "cshwshash.mm"
include "adantr.mm"
include "orcomd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "adantl.mm"
include "mpbird.mm"
include "eleq1.mm"
include "rexeqdv.mm"
include "rabbidv.mm"
include "eqeq2.mm"
include "orbi2d.mm"
include "imbi12d.mm"
include "eleq2s.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "com12.mm"
include "syl6bi.mm"
include "pm2.43i.mm"

theorem hashecclwwlkn1
  let vu: setvar u
  let vt: setvar t
  let c.sm: class .~
  let cU: class U
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vz: setvar z
  let vk: setvar k
  let cX: class X
  let cB: class B
  let cY: class Y
  assume erclwwlkn.w: |- W = ( N ClWWalksN G )
  assume erclwwlkn.r: |- .~ = { <. t , u >. | ( t e. W /\ u e. W /\ E. n e. ( 0 ... N ) t = ( u cyclShift n ) ) }

  disjoint W t
  disjoint W u
  disjoint t u
  disjoint N n
  disjoint N u
  disjoint N t
  disjoint n u
  disjoint n t
  disjoint W n
  disjoint G n
  disjoint G u
  disjoint U n
  disjoint U u
  disjoint N x
  disjoint n x
  disjoint u x
  disjoint t x
  disjoint n y
  disjoint t y
  disjoint u y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint x y
  disjoint N m
  disjoint n z
  disjoint t z
  disjoint u z
  disjoint y z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m z
  disjoint x z
  disjoint N k
  disjoint W k
  disjoint W m
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint W x
  disjoint G x
  disjoint X x
  disjoint B x
  disjoint B y
  disjoint N y
  disjoint W y
  disjoint X y
  disjoint G k
  disjoint X k
  disjoint X m
  disjoint X n
  disjoint Y k
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint Y y
  disjoint G m
  disjoint G y
  disjoint m u
  disjoint U m
  disjoint U x
  disjoint U y
  assert |- ( ( N e. Prime /\ U e. ( W /. .~ ) ) -> ( ( # ` U ) = 1 \/ ( # ` U ) = N ) )

  proof
    cU
    cW
    c.sm
    cqs
    #
    wcel
    #
    cN
    cprime
    wcel
    #
    cU
    chash
    cfv
    #
    c1
    wceq
    #
    @3
    cN
    wceq
    #
    wo
    #
    @1
    @2
    @6
    wi
    #
    @1
    @1
    cU
    vy
    cv
    #
    vx
    cv
    #
    vn
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vn
    cc0
    cN
    cfz
    co
    wrex
    #
    vy
    cW
    crab
    #
    wceq
    #
    vx
    cW
    wrex
    #
    @7
    vx
    vy
    vu
    vt
    cU
    c.sm
    vn
    cG
    cN
    cW
    @0
    erclwwlkn.w
    erclwwlkn.r
    eclclwwlkn1
    @2
    @16
    @6
    @2
    @15
    @6
    vx
    cW
    @2
    @9
    cW
    wcel
    #
    wa
    #
    @15
    cU
    @13
    vy
    cG
    cvtx
    cfv
    #
    cword
    #
    crab
    #
    wceq
    #
    @6
    @18
    @14
    @21
    cU
    @18
    @14
    @13
    vy
    cN
    cG
    cclwwlkn
    co
    #
    crab
    #
    @21
    cW
    @23
    wceq
    @14
    @24
    wceq
    @18
    erclwwlkn.w
    @13
    vy
    cW
    @23
    rabeq
    mp1i
    @2
    cN
    cn0
    wcel
    #
    @9
    @23
    wcel
    #
    @24
    @21
    wceq
    @17
    @2
    cN
    cN
    prmnn
    #
    nnnn0d
    @17
    @26
    cW
    @23
    @9
    erclwwlkn.w
    eleq2i
    #
    biimpi
    vy
    vn
    cG
    cN
    @9
    clwwlknscsh
    syl2an
    eqtrd
    eqeq2d
    @18
    @22
    cU
    @12
    vn
    cc0
    cN
    cfzo
    co
    #
    wrex
    #
    vy
    @20
    crab
    #
    wceq
    #
    @6
    @18
    @21
    @31
    cU
    @18
    @9
    @20
    wcel
    #
    @9
    c0
    wne
    #
    cN
    @9
    chash
    cfv
    #
    wceq
    #
    w3a
    #
    @21
    @31
    wceq
    @2
    @17
    @37
    @2
    cN
    cn
    wcel
    #
    @17
    @37
    wi
    @27
    @17
    @26
    @38
    @37
    @28
    @33
    @35
    cN
    wceq
    #
    wa
    #
    @38
    @37
    @26
    @40
    @38
    @37
    @40
    @38
    wa
    #
    @33
    @34
    @36
    @33
    @39
    @38
    simpll
    @38
    @40
    @34
    @38
    @25
    cN
    cc0
    wne
    #
    @40
    @34
    wi
    cN
    elnnne0
    @40
    @42
    @34
    @40
    cN
    cc0
    @9
    c0
    @39
    cN
    cc0
    wceq
    #
    @35
    cc0
    wceq
    #
    @33
    @9
    c0
    wceq
    @43
    @44
    wb
    cN
    @35
    cN
    @35
    cc0
    eqeq1
    eqcoms
    @9
    @20
    hasheq0
    sylan9bbr
    necon3bid
    biimpcd
    simplbiim
    impcom
    @41
    @35
    cN
    @33
    @39
    @38
    simplr
    eqcomd
    3jca
    ex
    cG
    cN
    @19
    @9
    @19
    eqid
    clwwlknbp
    #
    syl11
    syl5bi
    syl
    imp
    vy
    vn
    cN
    @19
    @9
    scshwfzeqfzo
    syl
    eqeq2d
    @17
    @2
    @32
    @6
    wi
    #
    @2
    @46
    wi
    #
    @9
    @23
    cW
    @26
    @40
    @47
    @45
    @40
    @47
    @35
    cprime
    wcel
    #
    cU
    @12
    vn
    cc0
    @35
    cfzo
    co
    #
    wrex
    #
    vy
    @20
    crab
    #
    wceq
    #
    @4
    @3
    @35
    wceq
    #
    wo
    #
    wi
    #
    wi
    #
    @33
    @56
    @39
    @33
    @48
    @55
    @33
    @48
    wa
    #
    @52
    @54
    @57
    @52
    wa
    #
    @54
    @51
    chash
    cfv
    #
    c1
    wceq
    #
    @59
    @35
    wceq
    #
    wo
    #
    @58
    @61
    @60
    @57
    @61
    @60
    wo
    @52
    vu
    vm
    @51
    @19
    @9
    @50
    @9
    vm
    cv
    #
    ccsh
    co
    #
    vu
    cv
    #
    wceq
    #
    vm
    @49
    wrex
    #
    vy
    vu
    @20
    @50
    @8
    @64
    wceq
    #
    vm
    @49
    wrex
    @8
    @65
    wceq
    #
    @67
    @12
    @68
    vn
    vm
    @49
    @10
    @63
    wceq
    @11
    @64
    @8
    @10
    @63
    @9
    ccsh
    oveq2
    eqeq2d
    cbvrexv
    @69
    @68
    @66
    vm
    @49
    @69
    @68
    @65
    @64
    wceq
    @66
    @8
    @65
    @64
    eqeq1
    @65
    @64
    eqcom
    syl6bb
    rexbidv
    syl5bb
    cbvrabv
    cshwshash
    adantr
    orcomd
    @52
    @54
    @62
    wb
    @57
    @52
    @4
    @60
    @53
    @61
    @52
    @3
    @59
    c1
    cU
    @51
    chash
    fveq2
    #
    eqeq1d
    @52
    @3
    @59
    @35
    @70
    eqeq1d
    orbi12d
    adantl
    mpbird
    ex
    ex
    adantr
    @39
    @47
    @56
    wb
    #
    @33
    @71
    cN
    @35
    @36
    @2
    @48
    @46
    @55
    cN
    @35
    cprime
    eleq1
    @36
    @32
    @52
    @6
    @54
    @36
    @31
    @51
    cU
    @36
    @30
    @50
    vy
    @20
    @36
    @12
    vn
    @29
    @49
    cN
    @35
    cc0
    cfzo
    oveq2
    rexeqdv
    rabbidv
    eqeq2d
    @36
    @5
    @53
    @4
    cN
    @35
    @3
    eqeq2
    orbi2d
    imbi12d
    imbi12d
    eqcoms
    adantl
    mpbird
    syl
    erclwwlkn.w
    eleq2s
    impcom
    sylbid
    sylbid
    rexlimdva
    com12
    syl6bi
    pm2.43i
    impcom
end
