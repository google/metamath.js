include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "vex.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "erclwwlkneqlen.mm"
include "3adant3.mm"
include "3adant1.mm"
include "ccsh.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "wb.mm"
include "erclwwlkneq.mm"
include "simpr1.mm"
include "simplr2.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "cclwwlkn.mm"
include "cvtx.mm"
include "cword.mm"
include "eqid.mm"
include "clwwlknbp.mm"
include "eqcom.mm"
include "biimpi.mm"
include "simpl2im.mm"
include "eleq2s.mm"
include "ad2antlr.mm"
include "simpld.mm"
include "adantl.mm"
include "simprr.mm"
include "cshwcsh2id.mm"
include "eqcoms.mm"
include "adantr.mm"
include "sylan9eq.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "anbi12d.mm"
include "rexeqdv.mm"
include "3imtr4d.mm"
include "mpancom.mm"
include "exp5l.mm"
include "imp41.mm"
include "rexlimdva.mm"
include "ex.mm"
include "syl7bi.mm"
include "syl5bi.mm"
include "exp31.mm"
include "com15.mm"
include "impcom.mm"
include "com13.mm"
include "3impia.mm"
include "3jca.mm"
include "3adant2.mm"
include "syl5ibrcom.mm"
include "com24.mm"
include "com4t.mm"
include "sylbid.mm"
include "com25.mm"
include "mpdd.mm"
include "impd.mm"
include "mp3an.mm"

theorem erclwwlkntr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  let vm: setvar m
  let vk: setvar k
  assume erclwwlkn.w: |- W = ( N ClWWalksN G )
  assume erclwwlkn.r: |- .~ = { <. t , u >. | ( t e. W /\ u e. W /\ E. n e. ( 0 ... N ) t = ( u cyclShift n ) ) }

  disjoint W t
  disjoint W u
  disjoint t u
  disjoint N n
  disjoint N u
  disjoint N t
  disjoint N x
  disjoint n u
  disjoint n t
  disjoint n x
  disjoint u x
  disjoint t x
  disjoint n y
  disjoint t y
  disjoint u y
  disjoint x y
  disjoint W n
  disjoint n z
  disjoint t z
  disjoint u z
  disjoint y z
  disjoint x z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint N m
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m z
  disjoint N k
  disjoint W k
  disjoint W m
  assert |- ( ( x .~ y /\ y .~ z ) -> x .~ z )

  proof
    vx
    cv
    #
    cvv
    wcel
    #
    vy
    cv
    #
    cvv
    wcel
    #
    vz
    cv
    #
    cvv
    wcel
    #
    @0
    @2
    c.sm
    wbr
    #
    @2
    @4
    c.sm
    wbr
    #
    wa
    @0
    @4
    c.sm
    wbr
    #
    wi
    vx
    vex
    vy
    vex
    vz
    vex
    @1
    @3
    @5
    w3a
    #
    @6
    @7
    @8
    @9
    @6
    @0
    chash
    cfv
    @2
    chash
    cfv
    #
    wceq
    #
    @7
    @8
    wi
    @1
    @3
    @6
    @11
    wi
    @5
    vu
    vt
    c.sm
    @0
    @2
    vn
    cG
    cN
    cW
    cvv
    cvv
    erclwwlkn.w
    erclwwlkn.r
    erclwwlkneqlen
    3adant3
    @9
    @7
    @11
    @6
    @8
    @9
    @7
    @10
    @4
    chash
    cfv
    #
    wceq
    #
    @11
    @6
    @8
    wi
    wi
    #
    @3
    @5
    @7
    @13
    wi
    @1
    vu
    vt
    c.sm
    @2
    @4
    vn
    cG
    cN
    cW
    cvv
    cvv
    erclwwlkn.w
    erclwwlkn.r
    erclwwlkneqlen
    3adant1
    @9
    @7
    @2
    cW
    wcel
    #
    @4
    cW
    wcel
    #
    @2
    @4
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
    #
    wrex
    #
    w3a
    #
    @13
    @14
    wi
    @3
    @5
    @7
    @22
    wb
    @1
    vu
    vt
    c.sm
    @2
    @4
    vn
    cG
    cN
    cW
    cvv
    cvv
    erclwwlkn.w
    erclwwlkn.r
    erclwwlkneq
    3adant1
    @9
    @6
    @13
    @11
    @22
    @8
    @9
    @6
    @0
    cW
    wcel
    #
    @15
    @0
    @2
    @17
    ccsh
    co
    #
    wceq
    #
    vn
    @20
    wrex
    #
    w3a
    #
    @13
    @11
    @22
    @8
    wi
    #
    wi
    wi
    @1
    @3
    @6
    @27
    wb
    @5
    vu
    vt
    c.sm
    @0
    @2
    vn
    cG
    cN
    cW
    cvv
    cvv
    erclwwlkn.w
    erclwwlkn.r
    erclwwlkneq
    3adant3
    @13
    @11
    @9
    @27
    @28
    @13
    @11
    @9
    @27
    @28
    wi
    wi
    @13
    @11
    wa
    #
    @22
    @27
    @9
    @8
    @29
    @22
    @27
    @9
    @8
    wi
    @29
    @22
    wa
    #
    @27
    wa
    #
    @8
    @9
    @23
    @16
    @0
    @18
    wceq
    #
    vn
    @20
    wrex
    #
    w3a
    #
    @31
    @23
    @16
    @33
    @30
    @23
    @15
    @26
    simpr1
    @15
    @16
    @21
    @29
    @27
    simplr2
    @27
    @30
    @33
    @23
    @15
    @26
    @30
    @33
    wi
    @30
    @26
    @23
    @15
    wa
    #
    @33
    @22
    @29
    @26
    @35
    @33
    wi
    wi
    #
    @16
    @21
    @29
    @36
    wi
    #
    @15
    @21
    @16
    @37
    @35
    @16
    @29
    @26
    @21
    @33
    @35
    @16
    @29
    @26
    @21
    @33
    wi
    #
    wi
    @26
    @0
    @2
    vm
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vm
    @20
    wrex
    #
    @35
    @16
    wa
    #
    @29
    wa
    #
    @38
    @25
    @41
    vn
    vm
    @20
    @17
    @39
    wceq
    @24
    @40
    @0
    @17
    @39
    @2
    ccsh
    oveq2
    eqeq2d
    cbvrexv
    @21
    @2
    @4
    vk
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vk
    @20
    wrex
    #
    @44
    @42
    @33
    @19
    @47
    vn
    vk
    @20
    @17
    @45
    wceq
    @18
    @46
    @2
    @17
    @45
    @4
    ccsh
    oveq2
    eqeq2d
    cbvrexv
    @44
    @41
    @48
    @33
    wi
    #
    vm
    @20
    @44
    @39
    @20
    wcel
    #
    wa
    #
    @41
    @49
    @51
    @41
    wa
    @47
    @33
    vk
    @20
    @44
    @50
    @41
    @45
    @20
    wcel
    #
    @47
    @33
    wi
    @44
    @50
    @41
    @52
    @47
    @33
    cN
    @12
    wceq
    #
    @44
    @50
    @41
    wa
    #
    @52
    @47
    wa
    #
    wa
    #
    @33
    wi
    @16
    @53
    @35
    @29
    @53
    @4
    cN
    cG
    cclwwlkn
    co
    #
    cW
    @4
    @57
    wcel
    #
    @4
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    @12
    cN
    wceq
    #
    @53
    cG
    cN
    @59
    @4
    @59
    eqid
    clwwlknbp
    #
    @61
    @53
    @12
    cN
    eqcom
    biimpi
    simpl2im
    erclwwlkn.w
    eleq2s
    ad2antlr
    @53
    @44
    wa
    #
    @39
    cc0
    @10
    cfz
    co
    #
    wcel
    #
    @41
    wa
    #
    @45
    cc0
    @12
    cfz
    co
    #
    wcel
    #
    @47
    wa
    #
    wa
    @32
    vn
    @67
    wrex
    #
    @56
    @33
    @63
    vx
    vy
    vz
    vk
    vm
    vn
    @59
    @44
    @60
    @53
    @16
    @60
    @35
    @29
    @60
    @4
    @57
    cW
    @58
    @60
    @61
    @62
    simpld
    erclwwlkn.w
    eleq2s
    ad2antlr
    adantl
    @53
    @43
    @29
    simprr
    cshwcsh2id
    @63
    @54
    @66
    @55
    @69
    @63
    @50
    @65
    @41
    @63
    @20
    @64
    @39
    @53
    @44
    @20
    @67
    @64
    cN
    @12
    cc0
    cfz
    oveq2
    #
    @29
    @67
    @64
    wceq
    #
    @43
    @13
    @72
    @11
    @72
    @12
    @10
    @12
    @10
    cc0
    cfz
    oveq2
    eqcoms
    adantr
    adantl
    sylan9eq
    eleq2d
    anbi1d
    @53
    @55
    @69
    wb
    @44
    @53
    @52
    @68
    @47
    @53
    @20
    @67
    @45
    @71
    eleq2d
    anbi1d
    adantr
    anbi12d
    @53
    @33
    @70
    wb
    @44
    @53
    @32
    vn
    @20
    @67
    @71
    rexeqdv
    adantr
    3imtr4d
    mpancom
    exp5l
    imp41
    rexlimdva
    ex
    rexlimdva
    syl7bi
    syl5bi
    exp31
    com15
    impcom
    3adant1
    impcom
    com13
    3impia
    impcom
    3jca
    @1
    @5
    @8
    @34
    wb
    @3
    vu
    vt
    c.sm
    @0
    @4
    vn
    cG
    cN
    cW
    cvv
    cvv
    erclwwlkn.w
    erclwwlkn.r
    erclwwlkneq
    3adant2
    syl5ibrcom
    exp31
    com24
    ex
    com4t
    sylbid
    com25
    sylbid
    mpdd
    com24
    mpdd
    impd
    mp3an
end
