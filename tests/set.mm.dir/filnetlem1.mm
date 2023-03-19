include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "sseq1d.mm"
include "sylan9bb.mm"
include "brab2a.mm"

theorem filnetlem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let vn: setvar n
  let cF: class F
  let cH: class H
  let vd: setvar d
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cX: class X
  assume filnet.h: |- H = U_ n e. F ( { n } X. n )
  assume filnet.d: |- D = { <. x , y >. | ( ( x e. H /\ y e. H ) /\ ( 1st ` y ) C_ ( 1st ` x ) ) }
  assume filnetlem1.a: |- A e. _V
  assume filnetlem1.b: |- B e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint H x
  disjoint H y
  disjoint B x
  disjoint B y
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
  assert |- ( A D B <-> ( ( A e. H /\ B e. H ) /\ ( 1st ` B ) C_ ( 1st ` A ) ) )

  proof
    vy
    cv
    #
    c1st
    cfv
    #
    vx
    cv
    #
    c1st
    cfv
    #
    wss
    #
    cB
    c1st
    cfv
    #
    cA
    c1st
    cfv
    #
    wss
    #
    vx
    vy
    cA
    cB
    cH
    cH
    cD
    @2
    cA
    wceq
    #
    @4
    @1
    @6
    wss
    @0
    cB
    wceq
    #
    @7
    @8
    @3
    @6
    @1
    @2
    cA
    c1st
    fveq2
    sseq2d
    @9
    @1
    @5
    @6
    @0
    cB
    c1st
    fveq2
    sseq1d
    sylan9bb
    filnet.d
    brab2a
end
