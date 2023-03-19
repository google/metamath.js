include "cid.mm"
include "cres.mm"
include "wss.mm"
include "cxp.mm"
include "cv.mm"
include "wbr.mm"
include "idref.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "ssid.mm"
include "vex.mm"
include "filnetlem1.mm"
include "mpbiran2.mm"
include "biimpri.mm"
include "anidms.mm"
include "mprgbir.mm"
include "copab.mm"
include "opabssxp.mm"
include "eqsstri.mm"
include "pm3.2i.mm"

theorem filnetlem2
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cA: class A
  let vd: setvar d
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let cX: class X
  assume filnet.h: |- H = U_ n e. F ( { n } X. n )
  assume filnet.d: |- D = { <. x , y >. | ( ( x e. H /\ y e. H ) /\ ( 1st ` y ) C_ ( 1st ` x ) ) }

  disjoint x y
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint H x
  disjoint H y
  disjoint A x
  disjoint A y
  disjoint d f
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
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
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint H d
  disjoint H f
  disjoint H m
  disjoint H t
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H z
  disjoint B x
  disjoint B y
  disjoint D d
  disjoint D f
  disjoint D t
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  disjoint X d
  disjoint X f
  disjoint X n
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X z
  assert |- ( ( _I |` H ) C_ D /\ D C_ ( H X. H ) )

  proof
    cid
    cH
    cres
    cD
    wss
    #
    cD
    cH
    cH
    cxp
    #
    wss
    @0
    vz
    cv
    #
    @2
    cD
    wbr
    #
    vz
    cH
    vz
    cH
    cD
    idref
    @2
    cH
    wcel
    #
    @3
    @3
    @4
    @4
    wa
    #
    @3
    @5
    @2
    c1st
    cfv
    #
    @6
    wss
    @6
    ssid
    vx
    vy
    @2
    @2
    cD
    vn
    cF
    cH
    filnet.h
    filnet.d
    vz
    vex
    #
    @7
    filnetlem1
    mpbiran2
    biimpri
    anidms
    mprgbir
    cD
    vx
    cv
    #
    cH
    wcel
    vy
    cv
    #
    cH
    wcel
    wa
    @9
    c1st
    cfv
    @8
    c1st
    cfv
    wss
    #
    wa
    vx
    vy
    copab
    @1
    filnet.d
    @10
    vx
    vy
    cH
    cH
    opabssxp
    eqsstri
    pm3.2i
end
