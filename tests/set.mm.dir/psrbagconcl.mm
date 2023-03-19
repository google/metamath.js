include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "wa.mm"
include "cn0.mm"
include "wf.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "cv.mm"
include "breq1.mm"
include "elrab2.mm"
include "sylib.mm"
include "simpld.mm"
include "psrbagf.mm"
include "syl2anc.mm"
include "simprd.mm"
include "psrbagcon.mm"
include "syl13anc.mm"
include "sylibr.mm"

theorem psrbagconcl
  let vy: setvar y
  let cD: class D
  let cS: class S
  let vf: setvar f
  let cF: class F
  let cI: class I
  let cV: class V
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let cG: class G
  let wph: wff ph
  let cB: class B
  let cY: class Y
  assume psrbag.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psrbagconf1o.1: |- S = { y e. D | y oR <_ F }

  disjoint f y
  disjoint F f
  disjoint F y
  disjoint V y
  disjoint I f
  disjoint I y
  disjoint D y
  disjoint X f
  disjoint X y
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
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
  disjoint V z
  disjoint I m
  disjoint I n
  disjoint I w
  disjoint I x
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
  disjoint D z
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
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
  assert |- ( ( I e. V /\ F e. D /\ X e. S ) -> ( F oF - X ) e. S )

  proof
    cI
    cV
    wcel
    #
    cF
    cD
    wcel
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cF
    cX
    cmin
    cof
    co
    #
    cD
    wcel
    @4
    cF
    cle
    cofr
    #
    wbr
    #
    wa
    #
    @4
    cS
    wcel
    @3
    @0
    @1
    cI
    cn0
    cX
    wf
    #
    cX
    cF
    @5
    wbr
    #
    @7
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    @3
    @0
    cX
    cD
    wcel
    #
    @8
    @10
    @3
    @11
    @9
    @3
    @2
    @11
    @9
    wa
    @0
    @1
    @2
    simp3
    vy
    cv
    #
    cF
    @5
    wbr
    #
    @9
    vy
    cX
    cD
    cS
    @12
    cX
    cF
    @5
    breq1
    psrbagconf1o.1
    elrab2
    sylib
    #
    simpld
    cD
    vf
    cX
    cI
    cV
    psrbag.d
    psrbagf
    syl2anc
    @3
    @11
    @9
    @14
    simprd
    cD
    vf
    cF
    cX
    cI
    cV
    psrbag.d
    psrbagcon
    syl13anc
    @13
    @6
    vy
    @4
    cD
    cS
    @12
    @4
    cF
    @5
    breq1
    psrbagconf1o.1
    elrab2
    sylibr
end
