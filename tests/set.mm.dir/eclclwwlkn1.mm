include "wcel.mm"
include "cqs.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "wceq.mm"
include "wrex.mm"
include "ccsh.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "crab.mm"
include "elqsecl.mm"
include "wa.mm"
include "w3a.mm"
include "wb.mm"
include "erclwwlknsym.mm"
include "impbii.mm"
include "a1i.mm"
include "abbidv.mm"
include "cvv.mm"
include "vex.mm"
include "erclwwlkneq.mm"
include "mp2an.mm"
include "3anan12.mm"
include "ibar.mm"
include "bicomd.mm"
include "adantl.mm"
include "syl5bb.mm"
include "df-rab.mm"
include "syl6eqr.mm"
include "3eqtrd.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "bitrd.mm"

theorem eclclwwlkn1
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vt: setvar t
  let cB: class B
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  let cX: class X
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
  disjoint .~ x
  disjoint .~ y
  disjoint W x
  disjoint G x
  disjoint X x
  disjoint B x
  disjoint B y
  disjoint N y
  disjoint W y
  disjoint X y
  disjoint m n
  disjoint m x
  disjoint m y
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
  disjoint .~ z
  assert |- ( B e. X -> ( B e. ( W /. .~ ) <-> E. x e. W B = { y e. W | E. n e. ( 0 ... N ) y = ( x cyclShift n ) } ) )

  proof
    cB
    cX
    wcel
    #
    cB
    cW
    c.sm
    cqs
    wcel
    cB
    vx
    cv
    #
    vy
    cv
    #
    c.sm
    wbr
    #
    vy
    cab
    #
    wceq
    #
    vx
    cW
    wrex
    cB
    @2
    @1
    vn
    cv
    ccsh
    co
    wceq
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
    vx
    vy
    cB
    c.sm
    cW
    cX
    elqsecl
    @0
    @5
    @8
    vx
    cW
    @0
    @1
    cW
    wcel
    #
    wa
    #
    @4
    @7
    cB
    @10
    @4
    @2
    @1
    c.sm
    wbr
    #
    vy
    cab
    @2
    cW
    wcel
    #
    @9
    @6
    w3a
    #
    vy
    cab
    #
    @7
    @10
    @3
    @11
    vy
    @3
    @11
    wb
    @10
    @3
    @11
    vx
    vy
    vu
    vt
    c.sm
    vn
    cG
    cN
    cW
    erclwwlkn.w
    erclwwlkn.r
    erclwwlknsym
    vy
    vx
    vu
    vt
    c.sm
    vn
    cG
    cN
    cW
    erclwwlkn.w
    erclwwlkn.r
    erclwwlknsym
    impbii
    a1i
    abbidv
    @10
    @11
    @13
    vy
    @11
    @13
    wb
    #
    @10
    @2
    cvv
    wcel
    @1
    cvv
    wcel
    @15
    vy
    vex
    vx
    vex
    vu
    vt
    c.sm
    @2
    @1
    vn
    cG
    cN
    cW
    cvv
    cvv
    erclwwlkn.w
    erclwwlkn.r
    erclwwlkneq
    mp2an
    a1i
    abbidv
    @10
    @14
    @12
    @6
    wa
    #
    vy
    cab
    @7
    @10
    @13
    @16
    vy
    @13
    @9
    @16
    wa
    #
    @10
    @16
    @12
    @9
    @6
    3anan12
    @9
    @17
    @16
    wb
    @0
    @9
    @16
    @17
    @9
    @16
    ibar
    bicomd
    adantl
    syl5bb
    abbidv
    @6
    vy
    cW
    df-rab
    syl6eqr
    3eqtrd
    eqeq2d
    rexbidva
    bitrd
end
