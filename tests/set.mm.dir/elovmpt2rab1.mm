include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "csb.mm"
include "w3a.mm"
include "cv.mm"
include "crab.mm"
include "elmpt2cl.mm"
include "wsbc.mm"
include "cmpt2.mm"
include "wceq.mm"
include "a1i.mm"
include "csbeq1.mm"
include "ad2antrl.mm"
include "wb.mm"
include "sbceq1a.mm"
include "sylan9bbr.mm"
include "adantl.mm"
include "rabeqbidv.mm"
include "eqidd.mm"
include "simpl.mm"
include "simpr.mm"
include "rabexg.mm"
include "syl.mm"
include "nfcv.mm"
include "nfel1.mm"
include "nfan.mm"
include "nfsbc1v.mm"
include "nfcsb.mm"
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

theorem elovmpt2rab1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let cM: class M
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume elovmpt2rab1.o: |- O = ( x e. _V , y e. _V |-> { z e. [_ x / m ]_ M | ph } )
  assume elovmpt2rab1.v: |- ( ( X e. _V /\ Y e. _V ) -> [_ X / m ]_ M e. _V )

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
  disjoint m z
  assert |- ( Z e. ( X O Y ) -> ( X e. _V /\ Y e. _V /\ Z e. [_ X / m ]_ M ) )

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
    vm
    cX
    cM
    csb
    #
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
    vm
    vx
    cv
    #
    cM
    csb
    #
    crab
    #
    cX
    cY
    cO
    cZ
    elovmpt2rab1.o
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
    @5
    crab
    #
    wcel
    #
    @7
    @2
    @3
    @13
    cZ
    @2
    vx
    vy
    cX
    cY
    cvv
    cvv
    @10
    @13
    cO
    cvv
    cvv
    cO
    vx
    vy
    cvv
    cvv
    @10
    cmpt2
    wceq
    @2
    elovmpt2rab1.o
    a1i
    @2
    @8
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
    @12
    vz
    @9
    @5
    @15
    @9
    @5
    wceq
    @2
    @16
    vm
    @8
    cX
    cM
    csbeq1
    ad2antrl
    @17
    wph
    @12
    wb
    @2
    @16
    wph
    @11
    @15
    @12
    wph
    vy
    cY
    sbceq1a
    @11
    vx
    cX
    sbceq1a
    sylan9bbr
    adantl
    rabeqbidv
    @2
    @15
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
    @5
    cvv
    wcel
    @13
    cvv
    wcel
    elovmpt2rab1.v
    @12
    vz
    @5
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
    #
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
    @20
    @19
    @12
    vx
    vz
    @5
    @11
    vx
    cX
    nfsbc1v
    vx
    vm
    cX
    cM
    @18
    vx
    cM
    nfcv
    nfcsb
    nfrab
    @12
    vy
    vz
    @5
    @11
    vy
    vx
    cX
    @20
    wph
    vy
    cY
    nfsbc1v
    nfsbc
    vy
    vm
    cX
    cM
    @20
    vy
    cM
    nfcv
    nfcsb
    nfrab
    ovmpt2dxf
    eleq2d
    @6
    @2
    @7
    @14
    @7
    @2
    @6
    @0
    @1
    @6
    df-3an
    simplbi2com
    @12
    vz
    cZ
    @5
    elrabi
    syl11
    sylbid
    mpcom
end
