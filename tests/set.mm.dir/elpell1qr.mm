include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell1qr.mm"
include "cfv.mm"
include "cv.mm"
include "csqrt.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "c1.mm"
include "wa.mm"
include "cn0.mm"
include "wrex.mm"
include "cr.mm"
include "crab.mm"
include "pell1qrval.mm"
include "eleq2d.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem elpell1qr
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cD: class D
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let cB: class B
  let vx: setvar x

  disjoint w z
  disjoint D z
  disjoint D w
  disjoint A z
  disjoint A w
  disjoint y z
  disjoint w y
  disjoint D y
  disjoint A y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint A b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint A c
  disjoint d e
  disjoint d f
  disjoint A d
  disjoint e f
  disjoint A e
  disjoint A f
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint a w
  disjoint b w
  disjoint c w
  disjoint d w
  disjoint e w
  disjoint f w
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint e z
  disjoint f z
  assert |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell1QR ` D ) <-> ( A e. RR /\ E. z e. NN0 E. w e. NN0 ( A = ( z + ( ( sqrt ` D ) x. w ) ) /\ ( ( z ^ 2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) ) ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell1qr
    cfv
    #
    wcel
    cA
    va
    cv
    #
    vz
    cv
    #
    cD
    csqrt
    cfv
    vw
    cv
    #
    cmul
    co
    caddc
    co
    #
    wceq
    #
    @3
    c2
    cexp
    co
    cD
    @4
    c2
    cexp
    co
    cmul
    co
    cmin
    co
    c1
    wceq
    #
    wa
    #
    vw
    cn0
    wrex
    vz
    cn0
    wrex
    #
    va
    cr
    crab
    #
    wcel
    cA
    cr
    wcel
    cA
    @5
    wceq
    #
    @7
    wa
    #
    vw
    cn0
    wrex
    vz
    cn0
    wrex
    #
    wa
    @0
    @1
    @10
    cA
    va
    vz
    vw
    cD
    pell1qrval
    eleq2d
    @9
    @13
    va
    cA
    cr
    @2
    cA
    wceq
    #
    @8
    @12
    vz
    vw
    cn0
    cn0
    @14
    @6
    @11
    @7
    @2
    cA
    @5
    eqeq1
    anbi1d
    2rexbidv
    elrab
    syl6bb
end
