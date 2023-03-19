include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "csn.mm"
include "wceq.mm"
include "cvtxdg.mm"
include "c1.mm"
include "cop.mm"
include "dmeqd.mm"
include "cpw.mm"
include "wcel.mm"
include "dmsnopg.mm"
include "syl.mm"
include "eqtrd.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cvtx.mm"
include "wf.mm"
include "pweqd.mm"
include "eleqtrrd.mm"
include "fveq2.mm"
include "breq2d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "fsnd.mm"
include "adantr.mm"
include "simpr.mm"
include "feq12d.mm"
include "mpbird.mm"
include "eqid.mm"
include "vtxdlfgrval.mm"
include "syl2anc.mm"
include "rabeq.mm"
include "adantl.mm"
include "fveq2d.mm"
include "c0.mm"
include "cif.mm"
include "eleq2d.mm"
include "rabsnif.mm"
include "fveq1d.mm"
include "fvsng.mm"
include "iftrued.mm"
include "syl5eq.mm"
include "hashsng.mm"
include "3eqtrd.mm"
include "mpdan.mm"

theorem 1hevtxdg1
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume 1hevtxdg0.i: |- ( ph -> ( iEdg ` G ) = { <. A , E >. } )
  assume 1hevtxdg0.v: |- ( ph -> ( Vtx ` G ) = V )
  assume 1hevtxdg0.a: |- ( ph -> A e. X )
  assume 1hevtxdg0.d: |- ( ph -> D e. V )
  assume 1hevtxdg1.e: |- ( ph -> E e. ~P V )
  assume 1hevtxdg1.n: |- ( ph -> D e. E )
  assume 1hevtxdg1.l: |- ( ph -> 2 <_ ( # ` E ) )


  assert |- ( ph -> ( ( VtxDeg ` G ) ` D ) = 1 )

  proof
    wph
    cG
    ciedg
    cfv
    #
    cdm
    #
    cA
    csn
    #
    wceq
    #
    cD
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    c1
    wceq
    wph
    @1
    cA
    cE
    cop
    csn
    #
    cdm
    #
    @2
    wph
    @0
    @6
    1hevtxdg0.i
    dmeqd
    wph
    cE
    cV
    cpw
    #
    wcel
    #
    @7
    @2
    wceq
    1hevtxdg1.e
    cA
    cE
    @8
    dmsnopg
    syl
    eqtrd
    wph
    @3
    wa
    #
    @5
    cD
    vx
    cv
    #
    @0
    cfv
    #
    wcel
    #
    vx
    @1
    crab
    #
    chash
    cfv
    #
    @13
    vx
    @2
    crab
    #
    chash
    cfv
    #
    c1
    @10
    @1
    c2
    @11
    chash
    cfv
    #
    cle
    wbr
    #
    vx
    cG
    cvtx
    cfv
    #
    cpw
    #
    crab
    #
    @0
    wf
    #
    cD
    @20
    wcel
    #
    @5
    @15
    wceq
    @10
    @23
    @2
    @22
    @6
    wf
    #
    wph
    @25
    @3
    wph
    cA
    cE
    cX
    @22
    1hevtxdg0.a
    wph
    cE
    @21
    wcel
    c2
    cE
    chash
    cfv
    #
    cle
    wbr
    #
    cE
    @22
    wcel
    wph
    cE
    @8
    @21
    1hevtxdg1.e
    wph
    @20
    cV
    1hevtxdg0.v
    pweqd
    eleqtrrd
    1hevtxdg1.l
    @19
    @27
    vx
    cE
    @21
    @11
    cE
    wceq
    @18
    @26
    c2
    cle
    @11
    cE
    chash
    fveq2
    breq2d
    elrab
    sylanbrc
    fsnd
    adantr
    @10
    @1
    @2
    @22
    @0
    @6
    wph
    @0
    @6
    wceq
    @3
    1hevtxdg0.i
    adantr
    wph
    @3
    simpr
    feq12d
    mpbird
    wph
    @24
    @3
    wph
    cD
    cV
    @20
    1hevtxdg0.d
    1hevtxdg0.v
    eleqtrrd
    adantr
    vx
    @1
    @4
    cD
    cG
    @0
    @20
    @20
    eqid
    @0
    eqid
    @1
    eqid
    @4
    eqid
    vtxdlfgrval
    syl2anc
    @10
    @14
    @16
    chash
    @3
    @14
    @16
    wceq
    wph
    @13
    vx
    @1
    @2
    rabeq
    adantl
    fveq2d
    wph
    @17
    c1
    wceq
    @3
    wph
    @17
    @2
    chash
    cfv
    #
    c1
    wph
    @16
    @2
    chash
    wph
    @16
    cD
    cA
    @0
    cfv
    #
    wcel
    #
    @2
    c0
    cif
    @2
    @13
    @30
    vx
    cA
    @11
    cA
    wceq
    @12
    @29
    cD
    @11
    cA
    @0
    fveq2
    eleq2d
    rabsnif
    wph
    @30
    @2
    c0
    wph
    cD
    cE
    @29
    1hevtxdg1.n
    wph
    @29
    cA
    @6
    cfv
    #
    cE
    wph
    cA
    @0
    @6
    1hevtxdg0.i
    fveq1d
    wph
    cA
    cX
    wcel
    #
    @9
    @31
    cE
    wceq
    1hevtxdg0.a
    1hevtxdg1.e
    cA
    cE
    cX
    @8
    fvsng
    syl2anc
    eqtrd
    eleqtrrd
    iftrued
    syl5eq
    fveq2d
    wph
    @32
    @28
    c1
    wceq
    1hevtxdg0.a
    cA
    cX
    hashsng
    syl
    eqtrd
    adantr
    3eqtrd
    mpdan
end
