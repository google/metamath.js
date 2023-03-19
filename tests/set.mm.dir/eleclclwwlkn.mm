include "cqs.mm"
include "wcel.mm"
include "cv.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "wa.mm"
include "wb.mm"
include "wi.mm"
include "crab.mm"
include "eclclwwlkn1.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "eleclclwwlknlem2.mm"
include "ex.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "expd.mm"
include "impcom.mm"
include "com12.mm"
include "ad2antlr.mm"
include "imp.mm"
include "syl5bb.mm"
include "anbi2d.mm"
include "eleq2.mm"
include "bibi1d.mm"
include "imbi12d.mm"
include "adantl.mm"
include "mpbird.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "pm2.43i.mm"

theorem eleclclwwlkn
  let vu: setvar u
  let vt: setvar t
  let cB: class B
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vz: setvar z
  let vk: setvar k
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
  disjoint X n
  disjoint Y n
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
  disjoint Y k
  disjoint Y m
  disjoint Y x
  disjoint Y y
  assert |- ( ( B e. ( W /. .~ ) /\ X e. B ) -> ( Y e. B <-> ( Y e. W /\ E. n e. ( 0 ... N ) Y = ( X cyclShift n ) ) ) )

  proof
    cB
    cW
    c.sm
    cqs
    #
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cY
    cW
    wcel
    #
    cY
    cX
    vn
    cv
    #
    ccsh
    co
    wceq
    vn
    cc0
    cN
    cfz
    co
    #
    wrex
    #
    wa
    #
    wb
    #
    @1
    @2
    @9
    wi
    #
    @1
    @1
    cB
    vy
    cv
    #
    vx
    cv
    #
    @5
    ccsh
    co
    #
    wceq
    #
    vn
    @6
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
    @10
    vx
    vy
    vu
    vt
    cB
    c.sm
    vn
    cG
    cN
    cW
    @0
    erclwwlkn.w
    erclwwlkn.r
    eclclwwlkn1
    @1
    @17
    @10
    vx
    cW
    @1
    @12
    cW
    wcel
    #
    wa
    #
    @17
    @10
    @19
    @17
    wa
    #
    @10
    cX
    @16
    wcel
    #
    cY
    @16
    wcel
    #
    @8
    wb
    #
    wi
    #
    @20
    @21
    @23
    @22
    @4
    cY
    @13
    wceq
    #
    vn
    @6
    wrex
    #
    wa
    @20
    @21
    wa
    #
    @8
    @15
    @26
    vy
    cY
    cW
    @11
    cY
    wceq
    @14
    @25
    vn
    @6
    @11
    cY
    @13
    eqeq1
    rexbidv
    elrab
    @27
    @26
    @7
    @4
    @26
    cY
    @12
    vk
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vk
    @6
    wrex
    #
    @27
    @7
    @25
    @30
    vn
    vk
    @6
    @5
    @28
    wceq
    @13
    @29
    cY
    @5
    @28
    @12
    ccsh
    oveq2
    eqeq2d
    cbvrexv
    @20
    @21
    @31
    @7
    wb
    #
    @18
    @21
    @32
    wi
    @1
    @17
    @21
    @18
    @32
    @21
    cX
    cW
    wcel
    #
    cX
    @13
    wceq
    #
    vn
    @6
    wrex
    #
    wa
    @18
    @32
    wi
    #
    @15
    @35
    vy
    cX
    cW
    @11
    cX
    wceq
    @14
    @34
    vn
    @6
    @11
    cX
    @13
    eqeq1
    rexbidv
    elrab
    @35
    @33
    @36
    @35
    @33
    @18
    @32
    @35
    cX
    @12
    vm
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vm
    @6
    wrex
    @33
    @18
    wa
    #
    @32
    wi
    #
    @34
    @39
    vn
    vm
    @6
    @5
    @37
    wceq
    @13
    @38
    cX
    @5
    @37
    @12
    ccsh
    oveq2
    eqeq2d
    cbvrexv
    @39
    @41
    vm
    @6
    @37
    @6
    wcel
    @39
    wa
    @40
    @32
    vx
    vm
    vk
    vn
    cG
    cN
    cW
    cX
    cY
    erclwwlkn.w
    eleclclwwlknlem2
    ex
    rexlimiva
    sylbi
    expd
    impcom
    sylbi
    com12
    ad2antlr
    imp
    syl5bb
    anbi2d
    syl5bb
    ex
    @17
    @10
    @24
    wb
    @19
    @17
    @2
    @21
    @9
    @23
    cB
    @16
    cX
    eleq2
    @17
    @3
    @22
    @8
    cB
    @16
    cY
    eleq2
    bibi1d
    imbi12d
    adantl
    mpbird
    ex
    rexlimdva
    sylbid
    pm2.43i
    imp
end
