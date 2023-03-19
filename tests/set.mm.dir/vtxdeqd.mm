include "cvtx.mm"
include "cfv.mm"
include "cv.mm"
include "ciedg.mm"
include "wcel.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "csn.mm"
include "wceq.mm"
include "cxad.mm"
include "co.mm"
include "cmpt.mm"
include "cvtxdg.mm"
include "dmeqd.mm"
include "fveq1d.mm"
include "eleq2d.mm"
include "rabeqbidv.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "vtxdgfval.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem vtxdeqd
  let wph: wff ph
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vx: setvar x
  assume vtxdeqd.g: |- ( ph -> G e. X )
  assume vtxdeqd.h: |- ( ph -> H e. Y )
  assume vtxdeqd.v: |- ( ph -> ( Vtx ` H ) = ( Vtx ` G ) )
  assume vtxdeqd.i: |- ( ph -> ( iEdg ` H ) = ( iEdg ` G ) )


  assert |- ( ph -> ( VtxDeg ` H ) = ( VtxDeg ` G ) )

  proof
    wph
    vu
    cH
    cvtx
    cfv
    #
    vu
    cv
    #
    vx
    cv
    #
    cH
    ciedg
    cfv
    #
    cfv
    #
    wcel
    #
    vx
    @3
    cdm
    #
    crab
    #
    chash
    cfv
    #
    @4
    @1
    csn
    #
    wceq
    #
    vx
    @6
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    cmpt
    #
    vu
    cG
    cvtx
    cfv
    #
    @1
    @2
    cG
    ciedg
    cfv
    #
    cfv
    #
    wcel
    #
    vx
    @16
    cdm
    #
    crab
    #
    chash
    cfv
    #
    @17
    @9
    wceq
    #
    vx
    @19
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    cmpt
    #
    cH
    cvtxdg
    cfv
    #
    cG
    cvtxdg
    cfv
    #
    wph
    vu
    @0
    @13
    @15
    @25
    vtxdeqd.v
    wph
    @8
    @21
    @12
    @24
    cxad
    wph
    @7
    @20
    chash
    wph
    @5
    @18
    vx
    @6
    @19
    wph
    @3
    @16
    vtxdeqd.i
    dmeqd
    #
    wph
    @4
    @17
    @1
    wph
    @2
    @3
    @16
    vtxdeqd.i
    fveq1d
    #
    eleq2d
    rabeqbidv
    fveq2d
    wph
    @11
    @23
    chash
    wph
    @10
    @22
    vx
    @6
    @19
    @29
    wph
    @4
    @17
    @9
    @30
    eqeq1d
    rabeqbidv
    fveq2d
    oveq12d
    mpteq12dv
    wph
    cH
    cY
    wcel
    @27
    @14
    wceq
    vtxdeqd.h
    vx
    vu
    @6
    cH
    @3
    @0
    cY
    @0
    eqid
    @3
    eqid
    @6
    eqid
    vtxdgfval
    syl
    wph
    cG
    cX
    wcel
    @28
    @26
    wceq
    vtxdeqd.g
    vx
    vu
    @19
    cG
    @16
    @15
    cX
    @15
    eqid
    @16
    eqid
    @19
    eqid
    vtxdgfval
    syl
    3eqtr4d
end
