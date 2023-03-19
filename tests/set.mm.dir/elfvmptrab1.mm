include "cfv.mm"
include "wcel.mm"
include "csb.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "wi.mm"
include "ne0i.mm"
include "ndmfv.mm"
include "necon1ai.mm"
include "wsbc.mm"
include "crab.mm"
include "cvv.mm"
include "wceq.mm"
include "cv.mm"
include "dmmptss.mm"
include "sseli.mm"
include "rabexg.mm"
include "3syl.mm"
include "nfcv.mm"
include "nfsbc1v.mm"
include "nfcsb.mm"
include "nfrab.mm"
include "csbeq1.mm"
include "sbceq1a.mm"
include "rabeqbidv.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "elrabi.mm"
include "anim12i.mm"
include "ex.mm"
include "sylbid.mm"
include "pm2.43i.mm"

theorem elfvmptrab1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let cF: class F
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  assume elfvmptrab1.f: |- F = ( x e. V |-> { y e. [_ x / m ]_ M | ph } )
  assume elfvmptrab1.v: |- ( X e. V -> [_ X / m ]_ M e. _V )

  disjoint M x
  disjoint M y
  disjoint x y
  disjoint V x
  disjoint X x
  disjoint X y
  disjoint Y y
  disjoint m y
  assert |- ( Y e. ( F ` X ) -> ( X e. V /\ Y e. [_ X / m ]_ M ) )

  proof
    cY
    cX
    cF
    cfv
    #
    wcel
    #
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
    #
    @1
    @0
    c0
    wne
    cX
    cF
    cdm
    #
    wcel
    #
    @1
    @5
    wi
    @0
    cY
    ne0i
    @7
    @0
    c0
    cX
    cF
    ndmfv
    necon1ai
    @7
    @1
    cY
    wph
    vx
    cX
    wsbc
    #
    vy
    @3
    crab
    #
    wcel
    #
    @5
    @7
    @0
    @9
    cY
    @7
    @2
    @9
    cvv
    wcel
    #
    @0
    @9
    wceq
    @6
    cV
    cX
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
    cF
    elfvmptrab1.f
    dmmptss
    sseli
    #
    @7
    @2
    @3
    cvv
    wcel
    @11
    @15
    elfvmptrab1.v
    @8
    vy
    @3
    cvv
    rabexg
    3syl
    vx
    cX
    @14
    @9
    cV
    cF
    cvv
    vx
    cX
    nfcv
    #
    @8
    vx
    vy
    @3
    wph
    vx
    cX
    nfsbc1v
    vx
    vm
    cX
    cM
    @16
    vx
    cM
    nfcv
    nfcsb
    nfrab
    @12
    cX
    wceq
    wph
    @8
    vy
    @13
    @3
    vm
    @12
    cX
    cM
    csbeq1
    wph
    vx
    cX
    sbceq1a
    rabeqbidv
    elfvmptrab1.f
    fvmptf
    syl2anc
    eleq2d
    @7
    @10
    @5
    @7
    @2
    @10
    @4
    @15
    @8
    vy
    cY
    @3
    elrabi
    anim12i
    ex
    sylbid
    3syl
    pm2.43i
end
