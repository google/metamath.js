include "cdm.mm"
include "wcel.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "cfv.mm"
include "crab.mm"
include "wceq.mm"
include "pm2.1.mm"
include "imor.mm"
include "wa.mm"
include "ordir.mm"
include "c0.mm"
include "ndmfv.mm"
include "rabeqdv.mm"
include "rab0.mm"
include "syl6req.mm"
include "sylan9eq.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "cv.mm"
include "rabbidv.mm"
include "adantl.mm"
include "dmmpt.mm"
include "rabid2.mm"
include "fvex.mm"
include "rabex.mm"
include "mprgbir.mm"
include "eqtr4i.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "fvmptd.mm"
include "jaoi.mm"
include "sylbir.mm"
include "expcom.mm"
include "sylbi.mm"
include "mp2.mm"

theorem fvmptrabdm
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume fvmptrabdm.f: |- F = ( x e. V |-> { y e. ( G ` Y ) | ph } )
  assume fvmptrabdm.r: |- ( x = X -> ( ph <-> ps ) )
  assume fvmptrabdm.v: |- ( Y e. dom G -> X e. dom F )

  disjoint F x
  disjoint G x
  disjoint G y
  disjoint x y
  disjoint V x
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ps x
  disjoint k x
  assert |- ( F ` X ) = { y e. ( G ` Y ) | ps }

  proof
    cY
    cG
    cdm
    wcel
    #
    cX
    cF
    cdm
    #
    wcel
    #
    wi
    #
    @2
    wn
    #
    @2
    wo
    #
    cX
    cF
    cfv
    #
    wps
    vy
    cY
    cG
    cfv
    #
    crab
    #
    wceq
    #
    fvmptrabdm.v
    @2
    pm2.1
    @3
    @0
    wn
    #
    @2
    wo
    #
    @5
    @9
    wi
    @0
    @2
    imor
    @5
    @11
    @9
    @5
    @11
    wa
    @4
    @10
    wa
    #
    @2
    wo
    @9
    @4
    @10
    @2
    ordir
    @12
    @9
    @2
    @4
    @10
    @6
    c0
    @8
    cX
    cF
    ndmfv
    @10
    @8
    wps
    vy
    c0
    crab
    c0
    @10
    wps
    vy
    @7
    c0
    cY
    cG
    ndmfv
    rabeqdv
    wps
    vy
    rab0
    syl6req
    sylan9eq
    @2
    vx
    cX
    wph
    vy
    @7
    crab
    #
    @8
    cV
    cF
    cvv
    cF
    vx
    cV
    @13
    cmpt
    wceq
    @2
    fvmptrabdm.f
    a1i
    vx
    cv
    #
    cX
    wceq
    #
    @13
    @8
    wceq
    @2
    @15
    wph
    wps
    vy
    @7
    fvmptrabdm.r
    rabbidv
    adantl
    @2
    cX
    cV
    wcel
    @1
    cV
    cX
    @1
    @13
    cvv
    wcel
    #
    vx
    cV
    crab
    #
    cV
    vx
    cV
    @13
    cF
    fvmptrabdm.f
    dmmpt
    cV
    @17
    wceq
    @16
    vx
    cV
    @16
    vx
    cV
    rabid2
    @16
    @14
    cV
    wcel
    wph
    vy
    @7
    cY
    cG
    fvex
    #
    rabex
    a1i
    mprgbir
    eqtr4i
    eleq2i
    biimpi
    @8
    cvv
    wcel
    @2
    wps
    vy
    @7
    @18
    rabex
    a1i
    fvmptd
    jaoi
    sylbir
    expcom
    sylbi
    mp2
end
