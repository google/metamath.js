include "erclwwlknrel.mm"
include "erclwwlknsym.mm"
include "erclwwlkntr.mm"
include "erclwwlknref.mm"
include "iseri.mm"

theorem erclwwlkn
  let vu: setvar u
  let vt: setvar t
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
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
  assert |- .~ Er W

  proof
    vx
    vy
    vz
    cW
    c.sm
    vu
    vt
    c.sm
    vn
    cG
    cN
    cW
    erclwwlkn.w
    erclwwlkn.r
    erclwwlknrel
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
    vx
    vy
    vz
    vu
    vt
    c.sm
    vn
    cG
    cN
    cW
    erclwwlkn.w
    erclwwlkn.r
    erclwwlkntr
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
    erclwwlknref
    iseri
end
