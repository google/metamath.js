include "csu.mm"
include "cmpt2.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "c1st.mm"
include "csb.mm"
include "cmpt.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfcsb.mm"
include "nfsum.mm"
include "weq.mm"
include "wa.mm"
include "csbeq1a.mm"
include "sylan9eq.mm"
include "sumeq2sdv.mm"
include "cbvmpt2.mm"
include "cop.mm"
include "wceq.mm"
include "vex.mm"
include "op2ndd.mm"
include "csbeq1d.mm"
include "op1std.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "mpt2mpt.mm"
include "eqtr4i.mm"
include "ctopon.mm"
include "wcel.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"
include "fsumcn.mm"
include "syl5eqel.mm"

theorem fsum2cn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume fsumcn.3: |- K = ( TopOpen ` CCfld )
  assume fsumcn.4: |- ( ph -> J e. ( TopOn ` X ) )
  assume fsumcn.5: |- ( ph -> A e. Fin )
  assume fsum2cn.7: |- ( ph -> L e. ( TopOn ` Y ) )
  assume fsum2cn.8: |- ( ( ph /\ k e. A ) -> ( x e. X , y e. Y |-> B ) e. ( ( J tX L ) Cn K ) )

  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint J k
  disjoint J x
  disjoint J y
  disjoint L k
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint K k
  disjoint K x
  disjoint K y
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint Y k
  disjoint Y x
  disjoint Y y
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint L z
  disjoint ph w
  disjoint ph z
  disjoint K v
  disjoint K w
  disjoint K z
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B z
  assert |- ( ph -> ( x e. X , y e. Y |-> sum_ k e. A B ) e. ( ( J tX L ) Cn K ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cA
    cB
    vk
    csu
    #
    cmpt2
    #
    vz
    cX
    cY
    cxp
    #
    cA
    vy
    vz
    cv
    #
    c2nd
    cfv
    #
    vx
    @3
    c1st
    cfv
    #
    cB
    csb
    #
    csb
    #
    vk
    csu
    #
    cmpt
    #
    cJ
    cL
    ctx
    co
    #
    cK
    ccn
    co
    #
    @1
    vu
    vv
    cX
    cY
    cA
    vy
    vv
    cv
    #
    vx
    vu
    cv
    #
    cB
    csb
    #
    csb
    #
    vk
    csu
    #
    cmpt2
    @9
    vx
    vy
    vu
    vv
    cX
    cY
    @0
    @16
    vu
    @0
    nfcv
    vv
    @0
    nfcv
    vx
    cA
    @15
    vk
    vx
    cA
    nfcv
    vx
    vy
    @12
    @14
    vx
    @12
    nfcv
    vx
    @13
    cB
    nfcsb1v
    nfcsb
    #
    nfsum
    vy
    cA
    @15
    vk
    vy
    cA
    nfcv
    vy
    @12
    @14
    nfcsb1v
    #
    nfsum
    vx
    vu
    weq
    #
    vy
    vv
    weq
    #
    wa
    cA
    cB
    @15
    vk
    @19
    @20
    cB
    @14
    @15
    vx
    @13
    cB
    csbeq1a
    vy
    @12
    @14
    csbeq1a
    sylan9eq
    #
    sumeq2sdv
    cbvmpt2
    vu
    vv
    vz
    cX
    cY
    @8
    @16
    @3
    @13
    @12
    cop
    wceq
    #
    cA
    @7
    @15
    vk
    @22
    @7
    vy
    @12
    @6
    csb
    @15
    @22
    vy
    @4
    @12
    @6
    @13
    @12
    @3
    vu
    vex
    #
    vv
    vex
    #
    op2ndd
    csbeq1d
    @22
    vy
    @12
    @6
    @14
    @22
    vx
    @5
    @13
    cB
    @13
    @12
    @3
    @23
    @24
    op1std
    csbeq1d
    csbeq2dv
    eqtrd
    #
    sumeq2sdv
    mpt2mpt
    eqtr4i
    wph
    vz
    cA
    @7
    vk
    @10
    cK
    @2
    fsumcn.3
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cL
    cY
    ctopon
    cfv
    wcel
    @10
    @2
    ctopon
    cfv
    wcel
    fsumcn.4
    fsum2cn.7
    cJ
    cL
    cX
    cY
    txtopon
    syl2anc
    fsumcn.5
    wph
    vk
    cv
    cA
    wcel
    wa
    vz
    @2
    @7
    cmpt
    #
    vx
    vy
    cX
    cY
    cB
    cmpt2
    #
    @11
    @27
    vu
    vv
    cX
    cY
    @15
    cmpt2
    @26
    vx
    vy
    vu
    vv
    cX
    cY
    cB
    @15
    vu
    cB
    nfcv
    vv
    cB
    nfcv
    @17
    @18
    @21
    cbvmpt2
    vu
    vv
    vz
    cX
    cY
    @7
    @15
    @25
    mpt2mpt
    eqtr4i
    fsum2cn.8
    syl5eqelr
    fsumcn
    syl5eqel
end
