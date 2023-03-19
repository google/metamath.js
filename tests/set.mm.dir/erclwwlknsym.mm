include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "wbr.mm"
include "wi.mm"
include "vex.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "erclwwlkneqlen.mm"
include "ccsh.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "w3a.mm"
include "erclwwlkneq.mm"
include "simpl2.mm"
include "simpl1.mm"
include "cclwwlkn.mm"
include "cvtx.mm"
include "cword.mm"
include "eqid.mm"
include "clwwlknbp.mm"
include "eqcom.mm"
include "biimpi.mm"
include "simpl2im.mm"
include "eleq2s.mm"
include "adantr.mm"
include "clwwlknwrd.mm"
include "adantl.mm"
include "simprr.mm"
include "cshwcshid.mm"
include "oveq2.mm"
include "sylan9eq.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "rexeqdv.mm"
include "3imtr4d.mm"
include "mpancom.mm"
include "expd.mm"
include "rexlimdv.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "imp.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "sylibr.mm"
include "3jca.mm"
include "wb.mm"
include "ancoms.mm"
include "syl5ibr.mm"
include "sylbid.mm"
include "mpdd.mm"
include "mp2an.mm"

theorem erclwwlknsym
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vt: setvar t
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  let vm: setvar m
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
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint N m
  assert |- ( x .~ y -> y .~ x )

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
    @0
    @2
    c.sm
    wbr
    #
    @2
    @0
    c.sm
    wbr
    #
    wi
    vx
    vex
    vy
    vex
    @1
    @3
    wa
    #
    @4
    @0
    chash
    cfv
    #
    @2
    chash
    cfv
    #
    wceq
    #
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
    @6
    @4
    @0
    cW
    wcel
    #
    @2
    cW
    wcel
    #
    @0
    @2
    vn
    cv
    #
    ccsh
    co
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
    @9
    @5
    wi
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
    @6
    @16
    @9
    @5
    @16
    @9
    wa
    #
    @5
    @6
    @11
    @10
    @2
    @0
    @12
    ccsh
    co
    #
    wceq
    #
    vn
    @14
    wrex
    #
    w3a
    #
    @17
    @11
    @10
    @20
    @10
    @11
    @15
    @9
    simpl2
    @10
    @11
    @15
    @9
    simpl1
    @17
    @2
    @0
    vm
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vm
    @14
    wrex
    #
    @20
    @16
    @9
    @25
    @10
    @11
    @15
    @9
    @25
    wi
    @10
    @11
    wa
    #
    @9
    @15
    @25
    @26
    @9
    @15
    @25
    wi
    @26
    @9
    wa
    #
    @13
    @25
    vn
    @14
    @27
    @12
    @14
    wcel
    #
    @13
    @25
    cN
    @7
    wceq
    #
    @27
    @28
    @13
    wa
    #
    @25
    wi
    @26
    @29
    @9
    @10
    @29
    @11
    @29
    @0
    cN
    cG
    cclwwlkn
    co
    #
    cW
    @0
    @31
    wcel
    @0
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    @7
    cN
    wceq
    #
    @29
    cG
    cN
    @32
    @0
    @32
    eqid
    #
    clwwlknbp
    @34
    @29
    @7
    cN
    eqcom
    biimpi
    simpl2im
    erclwwlkn.w
    eleq2s
    adantr
    adantr
    @29
    @27
    wa
    #
    @12
    cc0
    @8
    cfz
    co
    #
    wcel
    #
    @13
    wa
    @24
    vm
    cc0
    @7
    cfz
    co
    #
    wrex
    @30
    @25
    @36
    vx
    vy
    vn
    vm
    @32
    @27
    @2
    @33
    wcel
    #
    @29
    @26
    @40
    @9
    @11
    @40
    @10
    @40
    @2
    @31
    cW
    cG
    cN
    @32
    @2
    @35
    clwwlknwrd
    erclwwlkn.w
    eleq2s
    adantl
    adantr
    adantl
    @29
    @26
    @9
    simprr
    cshwcshid
    @36
    @28
    @38
    @13
    @36
    @14
    @37
    @12
    @29
    @27
    @14
    @39
    @37
    cN
    @7
    cc0
    cfz
    oveq2
    #
    @9
    @39
    @37
    wceq
    @26
    @7
    @8
    cc0
    cfz
    oveq2
    adantl
    sylan9eq
    eleq2d
    anbi1d
    @36
    @24
    vm
    @14
    @39
    @29
    @14
    @39
    wceq
    @27
    @41
    adantr
    rexeqdv
    3imtr4d
    mpancom
    expd
    rexlimdv
    ex
    com23
    3impia
    imp
    @19
    @24
    vn
    vm
    @14
    @12
    @22
    wceq
    @18
    @23
    @2
    @12
    @22
    @0
    ccsh
    oveq2
    eqeq2d
    cbvrexv
    sylibr
    3jca
    @3
    @1
    @5
    @21
    wb
    vu
    vt
    c.sm
    @2
    @0
    vn
    cG
    cN
    cW
    cvv
    cvv
    erclwwlkn.w
    erclwwlkn.r
    erclwwlkneq
    ancoms
    syl5ibr
    expd
    sylbid
    mpdd
    mp2an
end
