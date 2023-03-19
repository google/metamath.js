include "cv.mm"
include "csqrt.mm"
include "cfv.mm"
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
include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "cpell1qr.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "2rexbidv.mm"
include "rabbidv.mm"
include "df-pell1qr.mm"
include "reex.mm"
include "rabex.mm"
include "fvmpt.mm"

theorem pell1qrval
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cD: class D
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let cB: class B
  let vx: setvar x

  disjoint y z
  disjoint w y
  disjoint D y
  disjoint w z
  disjoint D z
  disjoint D w
  disjoint A y
  disjoint A z
  disjoint A w
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
  assert |- ( D e. ( NN \ []NN ) -> ( Pell1QR ` D ) = { y e. RR | E. z e. NN0 E. w e. NN0 ( y = ( z + ( ( sqrt ` D ) x. w ) ) /\ ( ( z ^ 2 ) - ( D x. ( w ^ 2 ) ) ) = 1 ) } )

  proof
    va
    cD
    vy
    cv
    #
    vz
    cv
    #
    va
    cv
    #
    csqrt
    cfv
    #
    vw
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @1
    c2
    cexp
    co
    #
    @2
    @4
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
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
    vy
    cr
    crab
    @0
    @1
    cD
    csqrt
    cfv
    #
    @4
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @8
    cD
    @9
    cmul
    co
    #
    cmin
    co
    #
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
    vy
    cr
    crab
    cn
    csquarenn
    cdif
    cpell1qr
    @2
    cD
    wceq
    #
    @14
    @23
    vy
    cr
    @24
    @13
    @22
    vz
    vw
    cn0
    cn0
    @24
    @7
    @18
    @12
    @21
    @24
    @6
    @17
    @0
    @24
    @5
    @16
    @1
    caddc
    @24
    @3
    @15
    @4
    cmul
    @2
    cD
    csqrt
    fveq2
    oveq1d
    oveq2d
    eqeq2d
    @24
    @11
    @20
    c1
    @24
    @10
    @19
    @8
    cmin
    @2
    cD
    @9
    cmul
    oveq1
    oveq2d
    eqeq1d
    anbi12d
    2rexbidv
    rabbidv
    va
    vy
    vz
    vw
    df-pell1qr
    @23
    vy
    cr
    reex
    rabex
    fvmpt
end
