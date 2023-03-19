include "wcel.mm"
include "cusgr.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "crio.mm"
include "wi.mm"
include "cdm.mm"
include "wa.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "elrab2.mm"
include "biimpi.mm"
include "wreu.mm"
include "usgredgreu.mm"
include "3expb.mm"
include "wb.mm"
include "usgredg2vlem1.mm"
include "adantlr.mm"
include "ad4ant23.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "prcom.mm"
include "eqeq2i.mm"
include "reubii.mm"
include "ad3antrrr.mm"
include "preq1.mm"
include "eqeq2d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "exbiri.mm"
include "com13.mm"
include "eqcoms.mm"
include "pm2.43i.mm"
include "expdcom.mm"
include "mpancom.mm"
include "expcom.mm"
include "com23.mm"
include "mpcom.mm"
include "impcom.mm"

theorem usgredg2vlem2
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cE: class E
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let cY: class Y
  assume usgredg2v.v: |- V = ( Vtx ` G )
  assume usgredg2v.e: |- E = ( iEdg ` G )
  assume usgredg2v.a: |- A = { x e. dom E | N e. ( E ` x ) }

  disjoint Y x
  disjoint Y z
  disjoint x z
  disjoint I z
  disjoint E x
  disjoint E z
  disjoint x z
  disjoint G z
  disjoint N x
  disjoint N z
  disjoint V z
  assert |- ( ( G e. USGraph /\ Y e. A ) -> ( I = ( iota_ z e. V ( E ` Y ) = { z , N } ) -> ( E ` Y ) = { I , N } ) )

  proof
    cY
    cA
    wcel
    #
    cG
    cusgr
    wcel
    #
    cI
    cY
    cE
    cfv
    #
    vz
    cv
    #
    cN
    cpr
    #
    wceq
    #
    vz
    cV
    crio
    #
    wceq
    #
    @2
    cI
    cN
    cpr
    #
    wceq
    #
    wi
    #
    cY
    cE
    cdm
    #
    wcel
    #
    cN
    @2
    wcel
    #
    wa
    #
    @0
    @1
    @10
    wi
    @0
    @14
    cN
    vx
    cv
    #
    cE
    cfv
    #
    wcel
    @13
    vx
    cY
    @11
    cA
    @15
    cY
    wceq
    @16
    @2
    cN
    @15
    cY
    cE
    fveq2
    eleq2d
    usgredg2v.a
    elrab2
    biimpi
    @14
    @1
    @0
    @10
    @1
    @14
    @0
    @10
    wi
    #
    @2
    cN
    @3
    cpr
    #
    wceq
    #
    vz
    cV
    wreu
    #
    @1
    @14
    wa
    #
    @17
    @1
    @12
    @13
    @20
    vz
    cE
    cG
    cV
    cY
    cN
    usgredg2v.v
    usgredg2v.e
    usgredgreu
    3expb
    @7
    @20
    @21
    wa
    #
    @0
    @9
    @7
    @22
    @0
    wa
    #
    @9
    wi
    #
    @7
    @24
    wi
    @6
    cI
    @23
    @7
    @6
    cI
    wceq
    #
    @9
    @23
    @7
    @9
    @25
    @23
    @7
    wa
    #
    cI
    cV
    wcel
    #
    @5
    vz
    cV
    wreu
    #
    @9
    @25
    wb
    @26
    @27
    @6
    cV
    wcel
    #
    @21
    @0
    @29
    @20
    @7
    @1
    @0
    @29
    @14
    vx
    vz
    cA
    cE
    cG
    cN
    cV
    cY
    usgredg2v.v
    usgredg2v.e
    usgredg2v.a
    usgredg2vlem1
    adantlr
    ad4ant23
    @7
    @27
    @29
    wb
    @23
    cI
    @6
    cV
    eleq1
    adantl
    mpbird
    @20
    @28
    @21
    @0
    @7
    @20
    @28
    @19
    @5
    vz
    cV
    @18
    @4
    @2
    cN
    @3
    prcom
    eqeq2i
    reubii
    biimpi
    ad3antrrr
    @5
    @9
    vz
    cV
    cI
    @3
    cI
    wceq
    @4
    @8
    @2
    @3
    cI
    cN
    preq1
    eqeq2d
    riota2
    syl2anc
    exbiri
    com13
    eqcoms
    pm2.43i
    expdcom
    mpancom
    expcom
    com23
    mpcom
    impcom
end
