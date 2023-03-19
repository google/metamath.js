include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "cfv.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmpt.mm"
include "pserval.mm"
include "fveq1d.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem pserval2
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cX: class X
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vy: setvar y
  let vj: setvar j
  let cH: class H
  let wph: wff ph
  let vr: setvar r
  let cR: class R
  let cY: class Y
  assume pser.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint N n
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
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint A m
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
  disjoint X m
  disjoint X s
  disjoint X y
  disjoint j r
  disjoint j y
  disjoint G j
  disjoint k r
  disjoint G k
  disjoint m r
  disjoint G m
  disjoint r s
  disjoint r y
  disjoint G r
  disjoint G s
  disjoint G y
  disjoint N y
  disjoint R k
  disjoint R y
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Y m
  assert |- ( ( X e. CC /\ N e. NN0 ) -> ( ( G ` X ) ` N ) = ( ( A ` N ) x. ( X ^ N ) ) )

  proof
    cX
    cc
    wcel
    #
    cN
    cn0
    wcel
    cN
    cX
    cG
    cfv
    #
    cfv
    cN
    vy
    cn0
    vy
    cv
    #
    cA
    cfv
    #
    cX
    @2
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cfv
    cN
    cA
    cfv
    #
    cX
    cN
    cexp
    co
    #
    cmul
    co
    #
    @0
    cN
    @1
    @6
    vx
    cA
    vy
    vn
    cG
    cX
    pser.g
    pserval
    fveq1d
    vy
    cN
    @5
    @9
    cn0
    @6
    @2
    cN
    wceq
    @3
    @7
    @4
    @8
    cmul
    @2
    cN
    cA
    fveq2
    @2
    cN
    cX
    cexp
    oveq2
    oveq12d
    @6
    eqid
    @7
    @8
    cmul
    ovex
    fvmpt
    sylan9eq
end
