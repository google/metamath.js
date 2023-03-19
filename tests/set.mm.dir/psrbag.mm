include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "cvv.mm"
include "wb.mm"
include "nn0ex.mm"
include "elmapg.mm"
include "mpan.mm"
include "anbi1d.mm"
include "syl5bb.mm"

theorem psrbag
  let cD: class D
  let vf: setvar f
  let cF: class F
  let cI: class I
  let cV: class V
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let wph: wff ph
  let cS: class S
  let cB: class B
  let cX: class X
  let cY: class Y
  assume psrbag.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }

  disjoint F f
  disjoint I f
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
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
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint I m
  disjoint I n
  disjoint I w
  disjoint I x
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
  disjoint D x
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
  assert |- ( I e. V -> ( F e. D <-> ( F : I --> NN0 /\ ( `' F " NN ) e. Fin ) ) )

  proof
    cF
    cD
    wcel
    cF
    cn0
    cI
    cmap
    co
    #
    wcel
    #
    cF
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    wa
    cI
    cV
    wcel
    #
    cI
    cn0
    cF
    wf
    #
    @4
    wa
    vf
    cv
    #
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    @4
    vf
    cF
    @0
    cD
    @7
    cF
    wceq
    #
    @9
    @3
    cfn
    @10
    @8
    @2
    cn
    @7
    cF
    cnveq
    imaeq1d
    eleq1d
    psrbag.d
    elrab2
    @5
    @1
    @6
    @4
    cn0
    cvv
    wcel
    @5
    @1
    @6
    wb
    nn0ex
    cn0
    cI
    cF
    cvv
    cV
    elmapg
    mpan
    anbi1d
    syl5bb
end
