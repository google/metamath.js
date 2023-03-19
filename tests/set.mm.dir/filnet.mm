include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "wss.mm"
include "copab.mm"
include "eqid.mm"
include "filnetlem4.mm"

theorem filnet
  let vf: setvar f
  let cF: class F
  let cX: class X
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cH: class H
  let cB: class B
  let cD: class D

  disjoint d f
  disjoint F d
  disjoint F f
  disjoint X d
  disjoint X f
  disjoint x y
  disjoint A x
  disjoint A y
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
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
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
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint H d
  disjoint H f
  disjoint H m
  disjoint H t
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H x
  disjoint H y
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
  disjoint X n
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X z
  assert |- ( F e. ( Fil ` X ) -> E. d e. DirRel E. f ( f : dom d --> X /\ F = ( ( X FilMap f ) ` ran ( tail ` d ) ) ) )

  proof
    vx
    vy
    vx
    cv
    #
    vn
    cF
    vn
    cv
    #
    csn
    @1
    cxp
    ciun
    #
    wcel
    vy
    cv
    #
    @2
    wcel
    wa
    @3
    c1st
    cfv
    @0
    c1st
    cfv
    wss
    wa
    vx
    vy
    copab
    #
    vf
    vn
    cF
    @2
    cX
    vd
    @2
    eqid
    @4
    eqid
    filnetlem4
end
