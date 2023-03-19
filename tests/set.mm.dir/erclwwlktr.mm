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
include "erclwwlkeqlen.mm"
include "3adant3.mm"
include "3adant1.mm"
include "cclwwlk.mm"
include "ccsh.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "wb.mm"
include "erclwwlkeq.mm"
include "simpr1.mm"
include "simplr2.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "cvtx.mm"
include "cword.mm"
include "c0.mm"
include "wne.mm"
include "eqid.mm"
include "clwwlkbp.mm"
include "simp2d.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "cshwcsh2id.mm"
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

theorem erclwwlktr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  let vm: setvar m
  let vk: setvar k
  assume erclwwlk.r: |- .~ = { <. u , w >. | ( u e. ( ClWWalks ` G ) /\ w e. ( ClWWalks ` G ) /\ E. n e. ( 0 ... ( # ` w ) ) u = ( w cyclShift n ) ) }

  disjoint G n
  disjoint G u
  disjoint G w
  disjoint n u
  disjoint n w
  disjoint u w
  disjoint n x
  disjoint u x
  disjoint w x
  disjoint n y
  disjoint u y
  disjoint w y
  disjoint x y
  disjoint n z
  disjoint u z
  disjoint w z
  disjoint x z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint G k
  disjoint G m
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m z
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
    vw
    vu
    c.sm
    @0
    vn
    cG
    @2
    cvv
    cvv
    erclwwlk.r
    erclwwlkeqlen
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
    vw
    vu
    c.sm
    @2
    vn
    cG
    @4
    cvv
    cvv
    erclwwlk.r
    erclwwlkeqlen
    3adant1
    @9
    @7
    @2
    cG
    cclwwlk
    cfv
    #
    wcel
    #
    @4
    @15
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
    @12
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
    @23
    wb
    @1
    vw
    vu
    c.sm
    @2
    vn
    cG
    @4
    cvv
    cvv
    erclwwlk.r
    erclwwlkeq
    3adant1
    @9
    @6
    @13
    @11
    @23
    @8
    @9
    @6
    @0
    @15
    wcel
    #
    @16
    @0
    @2
    @18
    ccsh
    co
    #
    wceq
    #
    vn
    cc0
    @10
    cfz
    co
    #
    wrex
    #
    w3a
    #
    @13
    @11
    @23
    @8
    wi
    #
    wi
    wi
    @1
    @3
    @6
    @29
    wb
    @5
    vw
    vu
    c.sm
    @0
    vn
    cG
    @2
    cvv
    cvv
    erclwwlk.r
    erclwwlkeq
    3adant3
    @13
    @11
    @9
    @29
    @30
    @13
    @11
    @9
    @29
    @30
    wi
    wi
    @13
    @11
    wa
    #
    @23
    @29
    @9
    @8
    @31
    @23
    @29
    @9
    @8
    wi
    @31
    @23
    wa
    #
    @29
    wa
    #
    @8
    @9
    @24
    @17
    @0
    @19
    wceq
    vn
    @21
    wrex
    #
    w3a
    #
    @33
    @24
    @17
    @34
    @32
    @24
    @16
    @28
    simpr1
    @16
    @17
    @22
    @31
    @29
    simplr2
    @29
    @32
    @34
    @24
    @16
    @28
    @32
    @34
    wi
    @32
    @28
    @24
    @16
    wa
    #
    @34
    @23
    @31
    @28
    @36
    @34
    wi
    wi
    #
    @17
    @22
    @31
    @37
    wi
    #
    @16
    @22
    @17
    @38
    @36
    @17
    @31
    @28
    @22
    @34
    @36
    @17
    @31
    @28
    @22
    @34
    wi
    #
    wi
    @28
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
    @27
    wrex
    #
    @36
    @17
    wa
    #
    @31
    wa
    #
    @39
    @26
    @42
    vn
    vm
    @27
    @18
    @40
    wceq
    @25
    @41
    @0
    @18
    @40
    @2
    ccsh
    oveq2
    eqeq2d
    cbvrexv
    @22
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
    @21
    wrex
    #
    @45
    @43
    @34
    @20
    @48
    vn
    vk
    @21
    @18
    @46
    wceq
    @19
    @47
    @2
    @18
    @46
    @4
    ccsh
    oveq2
    eqeq2d
    cbvrexv
    @45
    @42
    @49
    @34
    wi
    #
    vm
    @27
    @45
    @40
    @27
    wcel
    #
    wa
    #
    @42
    @50
    @52
    @42
    wa
    @48
    @34
    vk
    @21
    @45
    @51
    @42
    @46
    @21
    wcel
    #
    @48
    @34
    wi
    @45
    @51
    @42
    @53
    @48
    @34
    @45
    vx
    vy
    vz
    vk
    vm
    vn
    cG
    cvtx
    cfv
    #
    @17
    @4
    @54
    cword
    wcel
    #
    @36
    @31
    @17
    cG
    cvv
    wcel
    @55
    @4
    c0
    wne
    cG
    @54
    @4
    @54
    eqid
    clwwlkbp
    simp2d
    ad2antlr
    @44
    @31
    simpr
    cshwcsh2id
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
    @35
    wb
    @3
    vw
    vu
    c.sm
    @0
    vn
    cG
    @4
    cvv
    cvv
    erclwwlk.r
    erclwwlkeq
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
