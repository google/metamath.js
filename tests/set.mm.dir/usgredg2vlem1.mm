include "wcel.mm"
include "cusgr.mm"
include "cdm.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "crio.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "elrab2.mm"
include "wreu.mm"
include "w3a.mm"
include "usgredgreu.mm"
include "prcom.mm"
include "eqeq2i.mm"
include "reubii.mm"
include "sylib.mm"
include "3expb.mm"
include "riotacl.mm"
include "syl.mm"
include "sylan2b.mm"

theorem usgredg2vlem1
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cY: class Y
  assume usgredg2v.v: |- V = ( Vtx ` G )
  assume usgredg2v.e: |- E = ( iEdg ` G )
  assume usgredg2v.a: |- A = { x e. dom E | N e. ( E ` x ) }

  disjoint Y x
  disjoint Y z
  disjoint x z
  disjoint E x
  disjoint E z
  disjoint x z
  disjoint G z
  disjoint N x
  disjoint N z
  disjoint V z
  assert |- ( ( G e. USGraph /\ Y e. A ) -> ( iota_ z e. V ( E ` Y ) = { z , N } ) e. V )

  proof
    cY
    cA
    wcel
    cG
    cusgr
    wcel
    #
    cY
    cE
    cdm
    #
    wcel
    #
    cN
    cY
    cE
    cfv
    #
    wcel
    #
    wa
    #
    @3
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
    cV
    wcel
    #
    cN
    vx
    cv
    #
    cE
    cfv
    #
    wcel
    @4
    vx
    cY
    @1
    cA
    @10
    cY
    wceq
    @11
    @3
    cN
    @10
    cY
    cE
    fveq2
    eleq2d
    usgredg2v.a
    elrab2
    @0
    @5
    wa
    @8
    vz
    cV
    wreu
    #
    @9
    @0
    @2
    @4
    @12
    @0
    @2
    @4
    w3a
    @3
    cN
    @6
    cpr
    #
    wceq
    #
    vz
    cV
    wreu
    @12
    vz
    cE
    cG
    cV
    cY
    cN
    usgredg2v.v
    usgredg2v.e
    usgredgreu
    @14
    @8
    vz
    cV
    @13
    @7
    @3
    cN
    @6
    prcom
    eqeq2i
    reubii
    sylib
    3expb
    @8
    vz
    cV
    riotacl
    syl
    sylan2b
end
