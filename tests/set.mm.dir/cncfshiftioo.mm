include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cioo.mm"
include "wrex.mm"
include "cc.mm"
include "crab.mm"
include "cmin.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccncf.mm"
include "wss.mm"
include "ioosscn.mm"
include "a1i.mm"
include "recnd.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cbvrabv.mm"
include "oveq1i.mm"
include "syl6eleq.mm"
include "eqid.mm"
include "cncfshift.mm"
include "iooshift.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "oveq1d.mm"
include "3eltr4d.mm"

theorem cncfshiftioo
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cF: class F
  let cG: class G
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume cncfshiftioo.a: |- ( ph -> A e. RR )
  assume cncfshiftioo.b: |- ( ph -> B e. RR )
  assume cncfshiftioo.c: |- C = ( A (,) B )
  assume cncfshiftioo.t: |- ( ph -> T e. RR )
  assume cncfshiftioo.d: |- D = ( ( A + T ) (,) ( B + T ) )
  assume cncfshiftioo.f: |- ( ph -> F e. ( C -cn-> CC ) )
  assume cncfshiftioo.g: |- G = ( x e. D |-> ( F ` ( x - T ) ) )

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint F x
  disjoint T x
  disjoint ph x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint T w
  disjoint T y
  disjoint T z
  disjoint ph y
  disjoint ph z
  disjoint k x
  assert |- ( ph -> G e. ( D -cn-> CC ) )

  proof
    wph
    vx
    vw
    cv
    #
    vz
    cv
    #
    cT
    caddc
    co
    #
    wceq
    #
    vz
    cA
    cB
    cioo
    co
    #
    wrex
    #
    vw
    cc
    crab
    #
    vx
    cv
    #
    cT
    cmin
    co
    cF
    cfv
    #
    cmpt
    #
    @6
    cc
    ccncf
    co
    cG
    cD
    cc
    ccncf
    co
    wph
    vx
    vy
    @4
    @6
    cT
    cF
    @9
    @4
    cc
    wss
    wph
    cA
    cB
    ioosscn
    a1i
    wph
    cT
    cncfshiftioo.t
    recnd
    @5
    @7
    vy
    cv
    #
    cT
    caddc
    co
    #
    wceq
    #
    vy
    @4
    wrex
    #
    vw
    vx
    cc
    @0
    @7
    wceq
    #
    @5
    @7
    @2
    wceq
    #
    vz
    @4
    wrex
    @13
    @14
    @3
    @15
    vz
    @4
    @0
    @7
    @2
    eqeq1
    rexbidv
    @15
    @12
    vz
    vy
    @4
    @1
    @10
    wceq
    @2
    @11
    @7
    @1
    @10
    cT
    caddc
    oveq1
    eqeq2d
    cbvrexv
    syl6bb
    cbvrabv
    wph
    cF
    cC
    cc
    ccncf
    co
    @4
    cc
    ccncf
    co
    cncfshiftioo.f
    cC
    @4
    cc
    ccncf
    cncfshiftioo.c
    oveq1i
    syl6eleq
    @9
    eqid
    cncfshift
    wph
    cG
    vx
    cD
    @8
    cmpt
    @9
    cncfshiftioo.g
    wph
    vx
    cD
    @6
    @8
    wph
    cD
    cA
    cT
    caddc
    co
    cB
    cT
    caddc
    co
    cioo
    co
    @6
    cncfshiftioo.d
    wph
    vz
    vw
    cA
    cB
    cT
    cncfshiftioo.a
    cncfshiftioo.b
    cncfshiftioo.t
    iooshift
    syl5eq
    #
    mpteq1d
    syl5eq
    wph
    cD
    @6
    cc
    ccncf
    @16
    oveq1d
    3eltr4d
end
