include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "crrn.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "rrnval.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "fveq2d.mm"
include "adantl.mm"
include "simp2.mm"
include "simp3.mm"
include "fvexd.mm"
include "ovmpt2d.mm"

theorem rrnmval
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cX: class X
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vz: setvar z
  let cM: class M
  let wph: wff ph
  let cA: class A
  let cJ: class J
  let cP: class P
  let cR: class R
  let vt: setvar t
  assume rrnval.1: |- X = ( RR ^m I )

  disjoint G k
  disjoint I k
  disjoint X k
  disjoint F k
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint n x
  disjoint n y
  disjoint G n
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint I i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint I j
  disjoint k m
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint I m
  disjoint n z
  disjoint I n
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint M j
  disjoint M k
  disjoint M n
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint A k
  disjoint J x
  disjoint P j
  disjoint P k
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint R k
  disjoint R n
  disjoint X i
  disjoint X j
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint j t
  disjoint F j
  disjoint k t
  disjoint m t
  disjoint F m
  disjoint n t
  disjoint F n
  disjoint t x
  disjoint t y
  disjoint F t
  disjoint F x
  disjoint F y
  assert |- ( ( I e. Fin /\ F e. X /\ G e. X ) -> ( F ( Rn ` I ) G ) = ( sqrt ` sum_ k e. I ( ( ( F ` k ) - ( G ` k ) ) ^ 2 ) ) )

  proof
    cI
    cfn
    wcel
    #
    cF
    cX
    wcel
    #
    cG
    cX
    wcel
    #
    w3a
    #
    vx
    vy
    cF
    cG
    cX
    cX
    cI
    vk
    cv
    #
    vx
    cv
    #
    cfv
    #
    @4
    vy
    cv
    #
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    cI
    @4
    cF
    cfv
    #
    @4
    cG
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    cI
    crrn
    cfv
    #
    cvv
    @0
    @1
    @19
    vx
    vy
    cX
    cX
    @12
    cmpt2
    wceq
    @2
    vx
    vy
    vk
    cI
    cX
    rrnval.1
    rrnval
    3ad2ant1
    @5
    cF
    wceq
    #
    @7
    cG
    wceq
    #
    wa
    #
    @12
    @18
    wceq
    @3
    @22
    @11
    @17
    csqrt
    @22
    cI
    @10
    @16
    vk
    @22
    @9
    @15
    c2
    cexp
    @20
    @21
    @6
    @13
    @8
    @14
    cmin
    @4
    @5
    cF
    fveq1
    @4
    @7
    cG
    fveq1
    oveqan12d
    oveq1d
    sumeq2sdv
    fveq2d
    adantl
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @3
    @17
    csqrt
    fvexd
    ovmpt2d
end
