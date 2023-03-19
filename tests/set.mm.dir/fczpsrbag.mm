include "wcel.mm"
include "cc0.mm"
include "cmpt.mm"
include "weq.mm"
include "cif.mm"
include "wceq.mm"
include "ifid.mm"
include "eqcomi.mm"
include "a1i.mm"
include "mpteq2dv.mm"
include "cn0.mm"
include "0nn0.mm"
include "cv.mm"
include "snifpsrbag.mm"
include "mpan2.mm"
include "eqeltrd.mm"

theorem fczpsrbag
  let vx: setvar x
  let cD: class D
  let vf: setvar f
  let cI: class I
  let cV: class V
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let wph: wff ph
  let cS: class S
  let cB: class B
  let cX: class X
  let cY: class Y
  assume psrbag.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }

  disjoint f x
  disjoint V x
  disjoint I f
  disjoint I x
  disjoint D x
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint V m
  disjoint V n
  disjoint V y
  disjoint V z
  disjoint I m
  disjoint I n
  disjoint I w
  disjoint I y
  disjoint I z
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S z
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint D j
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint X f
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y k
  disjoint Y m
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( I e. V -> ( x e. I |-> 0 ) e. D )

  proof
    cI
    cV
    wcel
    #
    vx
    cI
    cc0
    cmpt
    vx
    cI
    vx
    vn
    weq
    #
    cc0
    cc0
    cif
    #
    cmpt
    #
    cD
    @0
    vx
    cI
    cc0
    @2
    cc0
    @2
    wceq
    @0
    @2
    cc0
    @1
    cc0
    ifid
    eqcomi
    a1i
    mpteq2dv
    @0
    cc0
    cn0
    wcel
    @3
    cD
    wcel
    0nn0
    vx
    cD
    vf
    cI
    cc0
    cV
    vn
    cv
    psrbag.d
    snifpsrbag
    mpan2
    eqeltrd
end
