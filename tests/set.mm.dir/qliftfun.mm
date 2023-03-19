include "wfun.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wbr.mm"
include "wal.mm"
include "cqs.mm"
include "qliftlem.mm"
include "eceq1.mm"
include "fliftfun.mm"
include "wcel.mm"
include "wa.mm"
include "wer.mm"
include "adantr.mm"
include "simpr.mm"
include "ercl.mm"
include "ercl2.mm"
include "jca.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "simprl.mm"
include "erth.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "imbi1d.mm"
include "impexp.mm"
include "syl6bb.mm"
include "2albidv.mm"
include "r2al.mm"
include "syl6bbr.mm"
include "bitr4d.mm"

theorem qliftfun
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cX: class X
  let cY: class Y
  let vz: setvar z
  let cC: class C
  let cD: class D
  assume qlift.1: |- F = ran ( x e. X |-> <. [ x ] R , A >. )
  assume qlift.2: |- ( ( ph /\ x e. X ) -> A e. Y )
  assume qlift.3: |- ( ph -> R Er X )
  assume qlift.4: |- ( ph -> X e. _V )
  assume qliftfun.4: |- ( x = y -> A = B )

  disjoint A y
  disjoint B x
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint F y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint y z
  disjoint A z
  disjoint C x
  disjoint D x
  disjoint x z
  disjoint ph z
  disjoint R z
  disjoint F z
  disjoint X z
  disjoint Y z
  assert |- ( ph -> ( Fun F <-> A. x A. y ( x R y -> A = B ) ) )

  proof
    wph
    cF
    wfun
    vx
    cv
    #
    cR
    cec
    #
    vy
    cv
    #
    cR
    cec
    #
    wceq
    #
    cA
    cB
    wceq
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @0
    @2
    cR
    wbr
    #
    @5
    wi
    #
    vy
    wal
    vx
    wal
    #
    wph
    vx
    vy
    @1
    cA
    @3
    cB
    cX
    cR
    cqs
    cY
    cF
    cX
    qlift.1
    wph
    vx
    cA
    cR
    cF
    cX
    cY
    qlift.1
    qlift.2
    qlift.3
    qlift.4
    qliftlem
    qlift.2
    @0
    @2
    cR
    eceq1
    qliftfun.4
    fliftfun
    wph
    @10
    @0
    cX
    wcel
    #
    @2
    cX
    wcel
    #
    wa
    #
    @6
    wi
    #
    vy
    wal
    vx
    wal
    @7
    wph
    @9
    @14
    vx
    vy
    wph
    @9
    @13
    @4
    wa
    #
    @5
    wi
    @14
    wph
    @8
    @15
    @5
    wph
    @8
    @13
    @8
    wa
    @15
    wph
    @8
    @13
    wph
    @8
    @13
    wph
    @8
    wa
    #
    @11
    @12
    @16
    @0
    @2
    cR
    cX
    wph
    cX
    cR
    wer
    #
    @8
    qlift.3
    adantr
    #
    wph
    @8
    simpr
    #
    ercl
    @16
    @0
    @2
    cR
    cX
    @18
    @19
    ercl2
    jca
    ex
    pm4.71rd
    wph
    @13
    @8
    @4
    wph
    @13
    wa
    @0
    @2
    cR
    cX
    wph
    @17
    @13
    qlift.3
    adantr
    wph
    @11
    @12
    simprl
    erth
    pm5.32da
    bitrd
    imbi1d
    @13
    @4
    @5
    impexp
    syl6bb
    2albidv
    @6
    vx
    vy
    cX
    cX
    r2al
    syl6bbr
    bitr4d
end
