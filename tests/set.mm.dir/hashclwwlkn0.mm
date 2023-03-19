include "cvtx.mm"
include "cfv.mm"
include "cfn.mm"
include "wcel.mm"
include "wer.mm"
include "erclwwlkn.mm"
include "a1i.mm"
include "cclwwlkn.mm"
include "co.mm"
include "clwwlknfi.mm"
include "syl5eqel.mm"
include "qshash.mm"

theorem hashclwwlkn0
  let vx: setvar x
  let vu: setvar u
  let vt: setvar t
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  let vy: setvar y
  let vm: setvar m
  let vz: setvar z
  let vk: setvar k
  let cX: class X
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
  disjoint W n
  disjoint .~ x
  disjoint W x
  disjoint G x
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
  disjoint .~ y
  disjoint .~ z
  disjoint X x
  assert |- ( ( Vtx ` G ) e. Fin -> ( # ` W ) = sum_ x e. ( W /. .~ ) ( # ` x ) )

  proof
    cG
    cvtx
    cfv
    cfn
    wcel
    #
    vx
    cW
    c.sm
    cW
    c.sm
    wer
    @0
    vu
    vt
    c.sm
    vn
    cG
    cN
    cW
    erclwwlkn.w
    erclwwlkn.r
    erclwwlkn
    a1i
    @0
    cW
    cN
    cG
    cclwwlkn
    co
    cfn
    erclwwlkn.w
    cG
    cN
    clwwlknfi
    syl5eqel
    qshash
end
