include "cvtx.mm"
include "cfv.mm"
include "cfn.mm"
include "wcel.mm"
include "cpw.mm"
include "cqs.mm"
include "cclwwlkn.mm"
include "co.mm"
include "clwwlknfi.mm"
include "syl5eqel.mm"
include "pwfi.mm"
include "sylib.mm"
include "wer.mm"
include "erclwwlkn.mm"
include "a1i.mm"
include "qsss.mm"
include "ssfid.mm"

theorem qerclwwlknfi
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
  assert |- ( ( Vtx ` G ) e. Fin -> ( W /. .~ ) e. Fin )

  proof
    cG
    cvtx
    cfv
    cfn
    wcel
    #
    cW
    cpw
    #
    cW
    c.sm
    cqs
    @0
    cW
    cfn
    wcel
    @1
    cfn
    wcel
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
    cW
    pwfi
    sylib
    @0
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
    qsss
    ssfid
end
