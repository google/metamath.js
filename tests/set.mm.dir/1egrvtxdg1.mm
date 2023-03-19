include "cvtxdg.mm"
include "cfv.mm"
include "cv.mm"
include "ciedg.mm"
include "wcel.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "c1.mm"
include "cusgr.mm"
include "cvtx.mm"
include "wceq.mm"
include "eqid.mm"
include "eleqtrrd.mm"
include "usgr1e.mm"
include "vtxdusgrval.mm"
include "syl2anc.mm"
include "cpr.mm"
include "cop.mm"
include "csn.mm"
include "wa.mm"
include "dmeq.mm"
include "adantl.mm"
include "cvv.mm"
include "prex.mm"
include "dmsnopg.mm"
include "mp1i.mm"
include "eqtrd.mm"
include "wb.mm"
include "fveq1.mm"
include "eleq2d.mm"
include "rabeqbidv.mm"
include "fveq2d.mm"
include "c0.mm"
include "cif.mm"
include "fveq2.mm"
include "rabsnif.mm"
include "prid1g.mm"
include "syl.mm"
include "fvsng.mm"
include "sylancl.mm"
include "iftrued.mm"
include "syl5eq.mm"
include "hashsng.mm"
include "adantr.mm"
include "mpdan.mm"

theorem 1egrvtxdg1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume 1egrvtxdg1.v: |- ( ph -> ( Vtx ` G ) = V )
  assume 1egrvtxdg1.a: |- ( ph -> A e. X )
  assume 1egrvtxdg1.b: |- ( ph -> B e. V )
  assume 1egrvtxdg1.c: |- ( ph -> C e. V )
  assume 1egrvtxdg1.n: |- ( ph -> B =/= C )
  assume 1egrvtxdg1.i: |- ( ph -> ( iEdg ` G ) = { <. A , { B , C } >. } )


  assert |- ( ph -> ( ( VtxDeg ` G ) ` B ) = 1 )

  proof
    wph
    cB
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cB
    vx
    cv
    #
    cG
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
    c1
    wph
    cG
    cusgr
    wcel
    cB
    cG
    cvtx
    cfv
    #
    wcel
    @1
    @8
    wceq
    wph
    cA
    cB
    cC
    cG
    @9
    cX
    @9
    eqid
    #
    1egrvtxdg1.a
    wph
    cB
    cV
    @9
    1egrvtxdg1.b
    1egrvtxdg1.v
    eleqtrrd
    #
    wph
    cC
    cV
    @9
    1egrvtxdg1.c
    1egrvtxdg1.v
    eleqtrrd
    1egrvtxdg1.i
    1egrvtxdg1.n
    usgr1e
    @11
    vx
    @6
    @0
    cB
    cG
    @3
    @9
    @10
    @3
    eqid
    @6
    eqid
    @0
    eqid
    vtxdusgrval
    syl2anc
    wph
    @3
    cA
    cB
    cC
    cpr
    #
    cop
    csn
    #
    wceq
    #
    @8
    c1
    wceq
    1egrvtxdg1.i
    wph
    @14
    wa
    #
    @8
    cB
    @2
    @13
    cfv
    #
    wcel
    #
    vx
    cA
    csn
    #
    crab
    #
    chash
    cfv
    #
    c1
    @15
    @7
    @19
    chash
    @15
    @5
    @17
    vx
    @6
    @18
    @15
    @6
    @13
    cdm
    #
    @18
    @14
    @6
    @21
    wceq
    wph
    @3
    @13
    dmeq
    adantl
    @12
    cvv
    wcel
    #
    @21
    @18
    wceq
    @15
    cB
    cC
    prex
    #
    cA
    @12
    cvv
    dmsnopg
    mp1i
    eqtrd
    @14
    @5
    @17
    wb
    wph
    @14
    @4
    @16
    cB
    @2
    @3
    @13
    fveq1
    eleq2d
    adantl
    rabeqbidv
    fveq2d
    wph
    @20
    c1
    wceq
    @14
    wph
    @20
    @18
    chash
    cfv
    #
    c1
    wph
    @19
    @18
    chash
    wph
    @19
    cB
    cA
    @13
    cfv
    #
    wcel
    #
    @18
    c0
    cif
    @18
    @17
    @26
    vx
    cA
    @2
    cA
    wceq
    @16
    @25
    cB
    @2
    cA
    @13
    fveq2
    eleq2d
    rabsnif
    wph
    @26
    @18
    c0
    wph
    cB
    @12
    @25
    wph
    cB
    cV
    wcel
    cB
    @12
    wcel
    1egrvtxdg1.b
    cB
    cC
    cV
    prid1g
    syl
    wph
    cA
    cX
    wcel
    #
    @22
    @25
    @12
    wceq
    1egrvtxdg1.a
    @23
    cA
    @12
    cX
    cvv
    fvsng
    sylancl
    eleqtrrd
    iftrued
    syl5eq
    fveq2d
    wph
    @27
    @24
    c1
    wceq
    1egrvtxdg1.a
    cA
    cX
    hashsng
    syl
    eqtrd
    adantr
    eqtrd
    mpdan
    eqtrd
end
