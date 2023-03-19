include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cfv.mm"
include "wrel.mm"
include "cv.mm"
include "coc.mm"
include "wceq.mm"
include "cltrn.mm"
include "crio.mm"
include "ctendo.mm"
include "copab.mm"
include "relopab.mm"
include "catm.mm"
include "cple.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "eqid.mm"
include "dicdmN.mm"
include "eleq2d.mm"
include "breq1.mm"
include "notbid.mm"
include "elrab.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "dicval.mm"
include "syldan.mm"
include "releqd.mm"
include "mpbiri.mm"
include "ex.mm"
include "c0.mm"
include "rel0.mm"
include "ndmfv.mm"
include "pm2.61d1.mm"

theorem dicvalrelN
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  let vs: setvar s
  assume dicvalrel.h: |- H = ( LHyp ` K )
  assume dicvalrel.i: |- I = ( ( DIsoC ` K ) ` W )


  assert |- ( ( K e. V /\ W e. H ) -> Rel ( I ` X ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cI
    cdm
    #
    wcel
    #
    cX
    cI
    cfv
    #
    wrel
    #
    @0
    @2
    @4
    @0
    @2
    wa
    #
    @4
    vf
    cv
    cW
    cK
    coc
    cfv
    cfv
    #
    vg
    cv
    cfv
    cX
    wceq
    vg
    cW
    cK
    cltrn
    cfv
    cfv
    #
    crio
    vs
    cv
    #
    cfv
    wceq
    @8
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wcel
    wa
    #
    vf
    vs
    copab
    #
    wrel
    @10
    vf
    vs
    relopab
    @5
    @3
    @11
    @0
    @2
    cX
    cK
    catm
    cfv
    #
    wcel
    cX
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    wn
    #
    wa
    #
    @3
    @11
    wceq
    @0
    @2
    @16
    @0
    @2
    cX
    vp
    cv
    #
    cW
    @13
    wbr
    #
    wn
    #
    vp
    @12
    crab
    #
    wcel
    @16
    @0
    @1
    @20
    cX
    @12
    cH
    cI
    cK
    @13
    cV
    cW
    vp
    @13
    eqid
    #
    @12
    eqid
    #
    dicvalrel.h
    dicvalrel.i
    dicdmN
    eleq2d
    @19
    @15
    vp
    cX
    @12
    @17
    cX
    wceq
    @18
    @14
    @17
    cX
    cW
    @13
    breq1
    notbid
    elrab
    syl6bb
    biimpa
    @12
    @6
    cX
    @7
    vf
    vg
    @9
    cH
    cI
    cK
    @13
    cV
    cW
    vs
    @21
    @22
    dicvalrel.h
    @6
    eqid
    @7
    eqid
    @9
    eqid
    dicvalrel.i
    dicval
    syldan
    releqd
    mpbiri
    ex
    @2
    wn
    #
    @4
    c0
    wrel
    rel0
    @23
    @3
    c0
    cX
    cI
    ndmfv
    releqd
    mpbiri
    pm2.61d1
end
