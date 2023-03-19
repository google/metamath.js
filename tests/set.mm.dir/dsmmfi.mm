include "wfn.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cdsmm.mm"
include "co.mm"
include "cprds.mm"
include "cbs.mm"
include "cfv.mm"
include "cress.mm"
include "eqid.mm"
include "dsmmval2.mm"
include "cv.mm"
include "c0g.mm"
include "ccom.mm"
include "cdif.mm"
include "cdm.mm"
include "crab.mm"
include "wral.mm"
include "wceq.mm"
include "wss.mm"
include "cvv.mm"
include "wn.mm"
include "c0.mm"
include "noel.mm"
include "reldmprds.mm"
include "ovprc1.mm"
include "fveq2d.mm"
include "base0.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "adantl.mm"
include "simplr.mm"
include "simpll.mm"
include "simpr.mm"
include "prdsbasfn.mm"
include "fndm.mm"
include "syl.mm"
include "eqeltrd.mm"
include "difss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "ssfi.mm"
include "sylancl.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "dsmmbas2.mm"
include "eqtr2d.mm"
include "oveq2d.mm"
include "ovex.mm"
include "ressid.mm"
include "syl6eq.mm"
include "syl5eq.mm"

theorem dsmmfi
  let cR: class R
  let cS: class S
  let cI: class I
  let vf: setvar f


  assert |- ( ( R Fn I /\ I e. Fin ) -> ( S (+)m R ) = ( S Xs_ R ) )

  proof
    cR
    cI
    wfn
    #
    cI
    cfn
    wcel
    #
    wa
    #
    cS
    cR
    cdsmm
    co
    #
    cS
    cR
    cprds
    co
    #
    @3
    cbs
    cfv
    #
    cress
    co
    #
    @4
    @5
    cR
    cS
    @5
    eqid
    dsmmval2
    @2
    @6
    @4
    @4
    cbs
    cfv
    #
    cress
    co
    #
    @4
    @2
    @5
    @7
    @4
    cress
    @2
    @7
    vf
    cv
    #
    c0g
    cR
    ccom
    #
    cdif
    #
    cdm
    #
    cfn
    wcel
    #
    vf
    @7
    crab
    #
    @5
    @2
    @13
    vf
    @7
    wral
    @7
    @14
    wceq
    @2
    @13
    vf
    @7
    @2
    @9
    @7
    wcel
    #
    wa
    #
    @9
    cdm
    #
    cfn
    wcel
    @12
    @17
    wss
    #
    @13
    @16
    @17
    cI
    cfn
    @16
    @9
    cI
    wfn
    @17
    cI
    wceq
    @16
    @7
    cR
    cS
    @9
    cI
    cvv
    cfn
    @4
    @4
    eqid
    #
    @7
    eqid
    #
    @15
    cS
    cvv
    wcel
    #
    @2
    @21
    @15
    @21
    wn
    #
    @15
    @9
    c0
    wcel
    @9
    noel
    @22
    @7
    c0
    @9
    @22
    @7
    c0
    cbs
    cfv
    c0
    @22
    @4
    c0
    cbs
    cS
    cR
    cprds
    reldmprds
    ovprc1
    fveq2d
    base0
    syl6eqr
    eleq2d
    mtbiri
    con4i
    adantl
    @0
    @1
    @15
    simplr
    #
    @0
    @1
    @15
    simpll
    @2
    @15
    simpr
    prdsbasfn
    cI
    @9
    fndm
    syl
    @23
    eqeltrd
    @11
    @9
    wss
    @18
    @9
    @10
    difss
    @11
    @9
    dmss
    ax-mp
    @17
    @12
    ssfi
    sylancl
    ralrimiva
    @13
    vf
    @7
    rabid2
    sylibr
    @14
    @4
    cR
    cS
    vf
    cI
    cfn
    @19
    @14
    eqid
    dsmmbas2
    eqtr2d
    oveq2d
    @4
    cvv
    wcel
    @8
    @4
    wceq
    cS
    cR
    cprds
    ovex
    @7
    @4
    cvv
    @20
    ressid
    ax-mp
    syl6eq
    syl5eq
end
