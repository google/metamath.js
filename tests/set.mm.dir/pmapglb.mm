include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "weq.mm"
include "wrex.mm"
include "cab.mm"
include "cv.mm"
include "ciin.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "equcom.mm"
include "anbi2i.mm"
include "ancom.mm"
include "bitri.mm"
include "exbii.mm"
include "vex.mm"
include "eleq1.mm"
include "ceqsexv.mm"
include "abbii.mm"
include "abid2.mm"
include "eqtr2i.mm"
include "fveq2i.mm"
include "wral.mm"
include "wceq.mm"
include "dfss3.mm"
include "pmapglbx.mm"
include "syl3an2b.mm"
include "syl5eq.mm"

theorem pmapglb
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cG: class G
  let cK: class K
  let cM: class M
  let vi: setvar i
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let cI: class I
  assume pmapglb.b: |- B = ( Base ` K )
  assume pmapglb.g: |- G = ( glb ` K )
  assume pmapglb.m: |- M = ( pmap ` K )

  disjoint B x
  disjoint K x
  disjoint S x
  disjoint i p
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint B i
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint B p
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G p
  disjoint G z
  disjoint I i
  disjoint I p
  disjoint I y
  disjoint I z
  disjoint K i
  disjoint K p
  disjoint K y
  disjoint K z
  disjoint S p
  disjoint S y
  disjoint S z
  assert |- ( ( K e. HL /\ S C_ B /\ S =/= (/) ) -> ( M ` ( G ` S ) ) = |^|_ x e. S ( M ` x ) )

  proof
    cK
    chlt
    wcel
    #
    cS
    cB
    wss
    #
    cS
    c0
    wne
    #
    w3a
    cS
    cG
    cfv
    #
    cM
    cfv
    vy
    vx
    weq
    #
    vx
    cS
    wrex
    #
    vy
    cab
    #
    cG
    cfv
    #
    cM
    cfv
    #
    vx
    cS
    vx
    cv
    #
    cM
    cfv
    ciin
    #
    @3
    @7
    cM
    cS
    @6
    cG
    @6
    vy
    cv
    #
    cS
    wcel
    #
    vy
    cab
    cS
    @5
    @12
    vy
    @5
    @9
    cS
    wcel
    #
    @4
    wa
    #
    vx
    wex
    #
    @12
    @4
    vx
    cS
    df-rex
    @15
    vx
    vy
    weq
    #
    @13
    wa
    #
    vx
    wex
    @12
    @14
    @17
    vx
    @14
    @13
    @16
    wa
    @17
    @4
    @16
    @13
    vy
    vx
    equcom
    anbi2i
    @13
    @16
    ancom
    bitri
    exbii
    @13
    @12
    vx
    @11
    vy
    vex
    @9
    @11
    cS
    eleq1
    ceqsexv
    bitri
    bitri
    abbii
    vy
    cS
    abid2
    eqtr2i
    fveq2i
    fveq2i
    @1
    @0
    @9
    cB
    wcel
    vx
    cS
    wral
    @2
    @8
    @10
    wceq
    vx
    cS
    cB
    dfss3
    vy
    cB
    @9
    vx
    cG
    cS
    cK
    cM
    pmapglb.b
    pmapglb.g
    pmapglb.m
    pmapglbx
    syl3an2b
    syl5eq
end
