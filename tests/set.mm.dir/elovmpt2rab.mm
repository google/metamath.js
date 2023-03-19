include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "w3a.mm"
include "crab.mm"
include "elmpt2cl.mm"
include "wsbc.mm"
include "cmpt2.mm"
include "wceq.mm"
include "a1i.mm"
include "cv.mm"
include "wb.mm"
include "sbceq1a.mm"
include "sylan9bbr.mm"
include "adantl.mm"
include "rabbidv.mm"
include "eqidd.mm"
include "simpl.mm"
include "simpr.mm"
include "rabexg.mm"
include "syl.mm"
include "nfcv.mm"
include "nfel1.mm"
include "nfan.mm"
include "nfsbc1v.mm"
include "nfrab.mm"
include "nfsbc.mm"
include "ovmpt2dxf.mm"
include "eleq2d.mm"
include "df-3an.mm"
include "simplbi2com.mm"
include "elrabi.mm"
include "syl11.mm"
include "sylbid.mm"
include "mpcom.mm"

theorem elovmpt2rab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume elovmpt2rab.o: |- O = ( x e. _V , y e. _V |-> { z e. M | ph } )
  assume elovmpt2rab.v: |- ( ( X e. _V /\ Y e. _V ) -> M e. _V )

  disjoint M x
  disjoint M y
  disjoint M z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z z
  assert |- ( Z e. ( X O Y ) -> ( X e. _V /\ Y e. _V /\ Z e. M ) )

  proof
    cX
    cvv
    wcel
    #
    cY
    cvv
    wcel
    #
    wa
    #
    cZ
    cX
    cY
    cO
    co
    #
    wcel
    #
    @0
    @1
    cZ
    cM
    wcel
    #
    w3a
    #
    vx
    vy
    cvv
    cvv
    wph
    vz
    cM
    crab
    #
    cX
    cY
    cO
    cZ
    elovmpt2rab.o
    elmpt2cl
    @2
    @4
    cZ
    wph
    vy
    cY
    wsbc
    #
    vx
    cX
    wsbc
    #
    vz
    cM
    crab
    #
    wcel
    #
    @6
    @2
    @3
    @10
    cZ
    @2
    vx
    vy
    cX
    cY
    cvv
    cvv
    @7
    @10
    cO
    cvv
    cvv
    cO
    vx
    vy
    cvv
    cvv
    @7
    cmpt2
    wceq
    @2
    elovmpt2rab.o
    a1i
    @2
    vx
    cv
    cX
    wceq
    #
    vy
    cv
    cY
    wceq
    #
    wa
    #
    wa
    wph
    @9
    vz
    cM
    @14
    wph
    @9
    wb
    @2
    @13
    wph
    @8
    @12
    @9
    wph
    vy
    cY
    sbceq1a
    @8
    vx
    cX
    sbceq1a
    sylan9bbr
    adantl
    rabbidv
    @2
    @12
    wa
    cvv
    eqidd
    @0
    @1
    simpl
    @0
    @1
    simpr
    @2
    cM
    cvv
    wcel
    @10
    cvv
    wcel
    elovmpt2rab.v
    @9
    vz
    cM
    cvv
    rabexg
    syl
    @0
    @1
    vx
    vx
    cX
    cvv
    vx
    cX
    nfcv
    nfel1
    vx
    cY
    cvv
    vx
    cY
    nfcv
    #
    nfel1
    nfan
    @0
    @1
    vy
    vy
    cX
    cvv
    vy
    cX
    nfcv
    #
    nfel1
    vy
    cY
    cvv
    vy
    cY
    nfcv
    nfel1
    nfan
    @16
    @15
    @9
    vx
    vz
    cM
    @8
    vx
    cX
    nfsbc1v
    vx
    cM
    nfcv
    nfrab
    @9
    vy
    vz
    cM
    @8
    vy
    vx
    cX
    @16
    wph
    vy
    cY
    nfsbc1v
    nfsbc
    vy
    cM
    nfcv
    nfrab
    ovmpt2dxf
    eleq2d
    @5
    @2
    @6
    @11
    @6
    @2
    @5
    @0
    @1
    @5
    df-3an
    simplbi2com
    @9
    vz
    cZ
    cM
    elrabi
    syl11
    sylbid
    mpcom
end
