include "cn0.mm"
include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmpt.mm"
include "cc.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "syl5eq.mm"
include "eqtri.mm"
include "nn0ex.mm"
include "mptex.mm"
include "fvmpt.mm"

theorem pserval
  let vx: setvar x
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vi: setvar i
  let vk: setvar k
  let vs: setvar s
  let vy: setvar y
  let vj: setvar j
  let cH: class H
  let wph: wff ph
  let vr: setvar r
  let cN: class N
  let cR: class R
  let cY: class Y
  assume pser.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )

  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint X m
  disjoint G m
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i s
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint k m
  disjoint k n
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m s
  disjoint m y
  disjoint n s
  disjoint n y
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint x y
  disjoint A y
  disjoint j m
  disjoint j s
  disjoint H j
  disjoint H m
  disjoint H s
  disjoint i j
  disjoint i ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph s
  disjoint X i
  disjoint X k
  disjoint X s
  disjoint X y
  disjoint j r
  disjoint j y
  disjoint G j
  disjoint k r
  disjoint G k
  disjoint m r
  disjoint r s
  disjoint r y
  disjoint G r
  disjoint G s
  disjoint G y
  disjoint N n
  disjoint N y
  disjoint R k
  disjoint R y
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Y m
  assert |- ( X e. CC -> ( G ` X ) = ( m e. NN0 |-> ( ( A ` m ) x. ( X ^ m ) ) ) )

  proof
    vy
    cX
    vm
    cn0
    vm
    cv
    #
    cA
    cfv
    #
    vy
    cv
    #
    @0
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    vm
    cn0
    @1
    cX
    @0
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    cc
    cG
    @2
    cX
    wceq
    #
    vm
    cn0
    @4
    @7
    @8
    @3
    @6
    @1
    cmul
    @2
    cX
    @0
    cexp
    oveq1
    oveq2d
    mpteq2dv
    cG
    vx
    cc
    vn
    cn0
    vn
    cv
    #
    cA
    cfv
    #
    vx
    cv
    #
    @9
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cmpt
    vy
    cc
    @5
    cmpt
    pser.g
    vx
    vy
    cc
    @14
    @5
    @11
    @2
    wceq
    #
    @14
    vm
    cn0
    @1
    @11
    @0
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    @5
    vn
    vm
    cn0
    @13
    @17
    @9
    @0
    wceq
    @10
    @1
    @12
    @16
    cmul
    @9
    @0
    cA
    fveq2
    @9
    @0
    @11
    cexp
    oveq2
    oveq12d
    cbvmptv
    @15
    vm
    cn0
    @17
    @4
    @15
    @16
    @3
    @1
    cmul
    @11
    @2
    @0
    cexp
    oveq1
    oveq2d
    mpteq2dv
    syl5eq
    cbvmptv
    eqtri
    vm
    cn0
    @7
    nn0ex
    mptex
    fvmpt
end
