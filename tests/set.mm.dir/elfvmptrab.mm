include "cfv.mm"
include "wcel.mm"
include "csb.mm"
include "wa.mm"
include "crab.mm"
include "cmpt.mm"
include "cv.mm"
include "wceq.mm"
include "csbconstg.mm"
include "eqcomd.mm"
include "rabeq.mm"
include "syl.mm"
include "mpteq2ia.mm"
include "eqtri.mm"
include "cvv.mm"
include "eqeltrd.mm"
include "elfvmptrab1.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "imdistani.mm"

theorem elfvmptrab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  let vm: setvar m
  assume elfvmptrab.f: |- F = ( x e. V |-> { y e. M | ph } )
  assume elfvmptrab.v: |- ( X e. V -> M e. _V )

  disjoint M x
  disjoint M y
  disjoint x y
  disjoint V x
  disjoint X x
  disjoint X y
  disjoint Y y
  disjoint M m
  disjoint m x
  disjoint m y
  assert |- ( Y e. ( F ` X ) -> ( X e. V /\ Y e. M ) )

  proof
    cY
    cX
    cF
    cfv
    wcel
    cX
    cV
    wcel
    #
    cY
    vm
    cX
    cM
    csb
    #
    wcel
    #
    wa
    @0
    cY
    cM
    wcel
    #
    wa
    wph
    vx
    vy
    vm
    cF
    cM
    cV
    cX
    cY
    cF
    vx
    cV
    wph
    vy
    cM
    crab
    #
    cmpt
    vx
    cV
    wph
    vy
    vm
    vx
    cv
    #
    cM
    csb
    #
    crab
    #
    cmpt
    elfvmptrab.f
    vx
    cV
    @4
    @7
    @5
    cV
    wcel
    #
    cM
    @6
    wceq
    @4
    @7
    wceq
    @8
    @6
    cM
    vm
    @5
    cM
    cV
    csbconstg
    eqcomd
    wph
    vy
    cM
    @6
    rabeq
    syl
    mpteq2ia
    eqtri
    @0
    @1
    cM
    cvv
    vm
    cX
    cM
    cV
    csbconstg
    #
    elfvmptrab.v
    eqeltrd
    elfvmptrab1
    @0
    @2
    @3
    @0
    @2
    @3
    @0
    @1
    cM
    cY
    @9
    eleq2d
    biimpd
    imdistani
    syl
end
