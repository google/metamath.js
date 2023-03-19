include "cqs.mm"
include "wcel.mm"
include "cumgr.mm"
include "cprime.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "ccsh.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "crab.mm"
include "eclclwwlkn1.mm"
include "cvtx.mm"
include "cword.mm"
include "cclwwlkn.mm"
include "rabeq.mm"
include "mp1i.mm"
include "cn0.mm"
include "prmnn.mm"
include "nnnn0d.mm"
include "adantl.mm"
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
include "fveq2.mm"
include "c2.mm"
include "cuz.mm"
include "simprl.mm"
include "prmuz2.mm"
include "umgr2cwwkdifex.mm"
include "syl3anc.mm"
include "oveq2.mm"
include "cbvrexv.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "cbvrabv.mm"
include "cshwshashnsame.mm"
include "ad2ant2rl.mm"
include "mpd.mm"
include "sylan9eqr.mm"
include "exp41.mm"
include "adantr.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "rexeqdv.mm"
include "rabbidv.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "mpbird.mm"
include "mpcom.mm"
include "eleq2s.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "com12.mm"
include "syl6bi.mm"
include "pm2.43i.mm"

theorem umgrhashecclwwlk
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
  let vi: setvar i
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
  disjoint G i
  disjoint i m
  disjoint i x
  disjoint i u
  assert |- ( ( G e. UMGraph /\ N e. Prime ) -> ( U e. ( W /. .~ ) -> ( # ` U ) = N ) )

  proof
    cU
    cW
    c.sm
    cqs
    #
    wcel
    #
    cG
    cumgr
    wcel
    #
    cN
    cprime
    wcel
    #
    wa
    #
    cU
    chash
    cfv
    #
    cN
    wceq
    #
    @1
    @4
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
    @4
    @16
    @6
    @4
    @15
    @6
    vx
    cW
    @4
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
    @4
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
    @3
    @25
    @2
    @3
    cN
    cN
    prmnn
    #
    nnnn0d
    adantl
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
    @4
    @17
    @37
    @4
    cN
    cn
    wcel
    #
    @17
    @37
    wi
    @3
    @38
    @2
    @27
    adantl
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
    @4
    @32
    @6
    wi
    #
    @4
    @46
    wi
    #
    @9
    @23
    cW
    @40
    @26
    @47
    @45
    @40
    @26
    @47
    wi
    #
    @9
    @35
    cG
    cclwwlkn
    co
    #
    wcel
    #
    @2
    @35
    cprime
    wcel
    #
    wa
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
    @5
    @35
    wceq
    #
    wi
    #
    wi
    #
    wi
    #
    @33
    @60
    @39
    @33
    @50
    @52
    @56
    @57
    @56
    @33
    @50
    wa
    #
    @52
    wa
    #
    @5
    @55
    chash
    cfv
    #
    @35
    cU
    @55
    chash
    fveq2
    @62
    vi
    cv
    @9
    cfv
    cc0
    @9
    cfv
    wne
    vi
    @53
    wrex
    #
    @63
    @35
    wceq
    #
    @62
    @2
    @35
    c2
    cuz
    cfv
    wcel
    #
    @50
    @64
    @61
    @2
    @51
    simprl
    @52
    @66
    @61
    @51
    @66
    @2
    @35
    prmuz2
    adantl
    adantl
    @33
    @50
    @52
    simplr
    vi
    cG
    @35
    @9
    umgr2cwwkdifex
    syl3anc
    @33
    @51
    @64
    @65
    wi
    @50
    @2
    vu
    vi
    vm
    @55
    @19
    @9
    @54
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
    @53
    wrex
    #
    vy
    vu
    @20
    @54
    @8
    @68
    wceq
    #
    vm
    @53
    wrex
    @8
    @69
    wceq
    #
    @71
    @12
    @72
    vn
    vm
    @53
    @10
    @67
    wceq
    @11
    @68
    @8
    @10
    @67
    @9
    ccsh
    oveq2
    eqeq2d
    cbvrexv
    @73
    @72
    @70
    vm
    @53
    @73
    @72
    @69
    @68
    wceq
    @70
    @8
    @69
    @68
    eqeq1
    @69
    @68
    eqcom
    syl6bb
    rexbidv
    syl5bb
    cbvrabv
    cshwshashnsame
    ad2ant2rl
    mpd
    sylan9eqr
    exp41
    adantr
    @39
    @48
    @60
    wb
    #
    @33
    @74
    cN
    @35
    @36
    @26
    @50
    @47
    @59
    @36
    @23
    @49
    @9
    cN
    @35
    cG
    cclwwlkn
    oveq1
    eleq2d
    @36
    @4
    @52
    @46
    @58
    @36
    @3
    @51
    @2
    cN
    @35
    cprime
    eleq1
    anbi2d
    @36
    @32
    @56
    @6
    @57
    @36
    @31
    @55
    cU
    @36
    @30
    @54
    vy
    @20
    @36
    @12
    vn
    @29
    @53
    cN
    @35
    cc0
    cfzo
    oveq2
    rexeqdv
    rabbidv
    eqeq2d
    cN
    @35
    @5
    eqeq2
    imbi12d
    imbi12d
    imbi12d
    eqcoms
    adantl
    mpbird
    mpcom
    erclwwlkn.w
    eleq2s
    impcom
    sylbid
    sylbid
    rexlimdva
    com12
    syl6bi
    pm2.43i
    com12
end
