include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "c0g.mm"
include "ccom.mm"
include "cdif.mm"
include "cdm.mm"
include "cfn.mm"
include "cbs.mm"
include "cfv.mm"
include "crab.mm"
include "cdsmm.mm"
include "co.mm"
include "wne.mm"
include "cprds.mm"
include "wceq.mm"
include "fveq2i.mm"
include "rabeq.mm"
include "ax-mp.mm"
include "simpll.mm"
include "fvco2.mm"
include "sylan.mm"
include "neeq2d.mm"
include "rabbidva.mm"
include "cvv.mm"
include "eqid.mm"
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
include "simpr.mm"
include "prdsbasfn.mm"
include "wf.mm"
include "fn0g.mm"
include "dffn2.mm"
include "mpbi.mm"
include "biimpi.mm"
include "fco.mm"
include "sylancr.mm"
include "ffn.mm"
include "syl.mm"
include "ad2antrr.mm"
include "fndmdif.mm"
include "syl2anc.mm"
include "fndm.mm"
include "3eqtr4d.mm"
include "eleq1d.mm"
include "syl5eq.mm"
include "fnex.mm"
include "dsmmbase.mm"
include "eqtrd.mm"

theorem dsmmbas2
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cI: class I
  let cV: class V
  let vx: setvar x
  assume dsmmbas2.p: |- P = ( S Xs_ R )
  assume dsmmbas2.b: |- B = { f e. ( Base ` P ) | dom ( f \ ( 0g o. R ) ) e. Fin }

  disjoint S f
  disjoint R f
  disjoint P f
  disjoint I f
  disjoint V f
  disjoint S x
  disjoint f x
  disjoint R x
  disjoint P x
  disjoint I x
  disjoint V x
  assert |- ( ( R Fn I /\ I e. V ) -> B = ( Base ` ( S (+)m R ) ) )

  proof
    cR
    cI
    wfn
    #
    cI
    cV
    wcel
    #
    wa
    #
    cB
    vf
    cv
    #
    c0g
    cR
    ccom
    #
    cdif
    cdm
    #
    cfn
    wcel
    #
    vf
    cP
    cbs
    cfv
    #
    crab
    #
    cS
    cR
    cdsmm
    co
    cbs
    cfv
    #
    dsmmbas2.b
    @2
    @8
    vx
    cv
    #
    @3
    cfv
    #
    @10
    cR
    cfv
    c0g
    cfv
    #
    wne
    #
    vx
    cR
    cdm
    #
    crab
    #
    cfn
    wcel
    #
    vf
    cS
    cR
    cprds
    co
    #
    cbs
    cfv
    #
    crab
    #
    @9
    @2
    @8
    @6
    vf
    @18
    crab
    #
    @19
    @7
    @18
    wceq
    @8
    @20
    wceq
    cP
    @17
    cbs
    dsmmbas2.p
    fveq2i
    @6
    vf
    @7
    @18
    rabeq
    ax-mp
    @2
    @6
    @16
    vf
    @18
    @2
    @3
    @18
    wcel
    #
    wa
    #
    @5
    @15
    cfn
    @22
    @11
    @10
    @4
    cfv
    #
    wne
    #
    vx
    cI
    crab
    #
    @13
    vx
    cI
    crab
    #
    @5
    @15
    @22
    @24
    @13
    vx
    cI
    @22
    @10
    cI
    wcel
    #
    wa
    @23
    @12
    @11
    @22
    @0
    @27
    @23
    @12
    wceq
    @0
    @1
    @21
    simpll
    #
    cI
    c0g
    cR
    @10
    fvco2
    sylan
    neeq2d
    rabbidva
    @22
    @3
    cI
    wfn
    @4
    cI
    wfn
    #
    @5
    @25
    wceq
    @22
    @18
    cR
    cS
    @3
    cI
    cvv
    cV
    @17
    @17
    eqid
    @18
    eqid
    @21
    cS
    cvv
    wcel
    #
    @2
    @30
    @21
    @30
    wn
    #
    @21
    @3
    c0
    wcel
    @3
    noel
    @31
    @18
    c0
    @3
    @31
    @18
    c0
    cbs
    cfv
    c0
    @31
    @17
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
    @21
    simplr
    @28
    @2
    @21
    simpr
    prdsbasfn
    @0
    @29
    @1
    @21
    @0
    cI
    cvv
    @4
    wf
    #
    @29
    @0
    cvv
    cvv
    c0g
    wf
    #
    cI
    cvv
    cR
    wf
    #
    @32
    c0g
    cvv
    wfn
    @33
    fn0g
    cvv
    c0g
    dffn2
    mpbi
    @0
    @34
    cI
    cR
    dffn2
    biimpi
    cI
    cvv
    cvv
    c0g
    cR
    fco
    sylancr
    cI
    cvv
    @4
    ffn
    syl
    ad2antrr
    vx
    cI
    @3
    @4
    fndmdif
    syl2anc
    @0
    @15
    @26
    wceq
    #
    @1
    @21
    @0
    @14
    cI
    wceq
    @35
    cI
    cR
    fndm
    @13
    vx
    @14
    cI
    rabeq
    syl
    ad2antrr
    3eqtr4d
    eleq1d
    rabbidva
    syl5eq
    @2
    cR
    cvv
    wcel
    @19
    @9
    wceq
    cI
    cV
    cR
    fnex
    vx
    @19
    cR
    cS
    vf
    cvv
    @19
    eqid
    dsmmbase
    syl
    eqtrd
    syl5eq
end
