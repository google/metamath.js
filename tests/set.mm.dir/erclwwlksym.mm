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
include "erclwwlkeqlen.mm"
include "cclwwlk.mm"
include "ccsh.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "w3a.mm"
include "erclwwlkeq.mm"
include "simpl2.mm"
include "simpl1.mm"
include "cvtx.mm"
include "cword.mm"
include "c0.mm"
include "wne.mm"
include "eqid.mm"
include "clwwlkbp.mm"
include "simp2d.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "cshwcshid.mm"
include "expd.mm"
include "rexlimdv.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "imp.mm"
include "weq.mm"
include "oveq2.mm"
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

theorem erclwwlksym
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vu: setvar u
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  let vm: setvar m
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
  disjoint m n
  disjoint m x
  disjoint m y
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
    @6
    @4
    @0
    cG
    cclwwlk
    cfv
    #
    wcel
    #
    @2
    @10
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
    @8
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
    @6
    @17
    @9
    @5
    @17
    @9
    wa
    #
    @5
    @6
    @12
    @11
    @2
    @0
    @13
    ccsh
    co
    #
    wceq
    #
    vn
    cc0
    @7
    cfz
    co
    #
    wrex
    #
    w3a
    #
    @18
    @12
    @11
    @22
    @11
    @12
    @16
    @9
    simpl2
    @11
    @12
    @16
    @9
    simpl1
    @18
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
    @21
    wrex
    #
    @22
    @17
    @9
    @27
    @11
    @12
    @16
    @9
    @27
    wi
    @11
    @12
    wa
    #
    @9
    @16
    @27
    @28
    @9
    @16
    @27
    wi
    @28
    @9
    wa
    #
    @14
    @27
    vn
    @15
    @29
    @13
    @15
    wcel
    @14
    @27
    @29
    vx
    vy
    vn
    vm
    cG
    cvtx
    cfv
    #
    @12
    @2
    @30
    cword
    wcel
    #
    @11
    @9
    @12
    cG
    cvv
    wcel
    @31
    @2
    c0
    wne
    cG
    @30
    @2
    @30
    eqid
    clwwlkbp
    simp2d
    ad2antlr
    @28
    @9
    simpr
    cshwcshid
    expd
    rexlimdv
    ex
    com23
    3impia
    imp
    @20
    @26
    vn
    vm
    @21
    vn
    vm
    weq
    @19
    @25
    @2
    @13
    @24
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
    @23
    wb
    vw
    vu
    c.sm
    @2
    vn
    cG
    @0
    cvv
    cvv
    erclwwlk.r
    erclwwlkeq
    ancoms
    syl5ibr
    expd
    sylbid
    mpdd
    mp2an
end
