include "cclwwlk.mm"
include "cfv.mm"
include "erclwwlkrel.mm"
include "erclwwlksym.mm"
include "erclwwlktr.mm"
include "erclwwlkref.mm"
include "iseri.mm"

theorem erclwwlk
  let vw: setvar w
  let vu: setvar u
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vk: setvar k
  let vz: setvar z
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
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint x y
  disjoint G k
  disjoint G m
  disjoint k m
  disjoint k n
  disjoint n z
  disjoint u z
  disjoint w z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m z
  disjoint x z
  disjoint G x
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint y z
  assert |- .~ Er ( ClWWalks ` G )

  proof
    vx
    vy
    vz
    cG
    cclwwlk
    cfv
    c.sm
    vw
    vu
    c.sm
    vn
    cG
    erclwwlk.r
    erclwwlkrel
    vx
    vy
    vw
    vu
    c.sm
    vn
    cG
    erclwwlk.r
    erclwwlksym
    vx
    vy
    vz
    vw
    vu
    c.sm
    vn
    cG
    erclwwlk.r
    erclwwlktr
    vx
    vw
    vu
    c.sm
    vn
    cG
    erclwwlk.r
    erclwwlkref
    iseri
end
