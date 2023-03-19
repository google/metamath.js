include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "ctrl.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "cple.mm"
include "eqid.mm"
include "id.mm"
include "wf1o.mm"
include "wf.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "cv.mm"
include "w3a.mm"
include "ccom.mm"
include "wceq.mm"
include "ltrnco.mm"
include "fvresi.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "coeq12d.mm"
include "eqtr4d.mm"
include "adantl.mm"
include "fveq2d.mm"
include "clat.mm"
include "cbs.mm"
include "wbr.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "trlcl.mm"
include "latref.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "istendod.mm"

theorem tendoidcl
  let cT: class T
  let cE: class E
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let cS: class S
  let cU: class U
  let cV: class V
  let cF: class F
  let cG: class G
  assume tendof.h: |- H = ( LHyp ` K )
  assume tendof.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendof.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> ( _I |` T ) e. E )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cid
    cT
    cres
    #
    cT
    vf
    vg
    cE
    cH
    cK
    cK
    cple
    cfv
    #
    chlt
    cW
    @5
    eqid
    #
    tendof.h
    tendof.t
    @3
    eqid
    #
    tendof.e
    @2
    id
    cT
    cT
    @4
    wf1o
    cT
    cT
    @4
    wf
    @2
    cT
    f1oi
    cT
    cT
    @4
    f1of
    mp1i
    @2
    vf
    cv
    #
    cT
    wcel
    #
    vg
    cv
    #
    cT
    wcel
    #
    w3a
    #
    @8
    @10
    ccom
    #
    @4
    cfv
    #
    @13
    @8
    @4
    cfv
    #
    @10
    @4
    cfv
    #
    ccom
    @12
    @13
    cT
    wcel
    @14
    @13
    wceq
    cT
    @8
    @10
    cH
    cK
    cW
    tendof.h
    tendof.t
    ltrnco
    cT
    @13
    fvresi
    syl
    @12
    @15
    @8
    @16
    @10
    @9
    @2
    @15
    @8
    wceq
    #
    @11
    cT
    @8
    fvresi
    #
    3ad2ant2
    @11
    @2
    @16
    @10
    wceq
    @9
    cT
    @10
    fvresi
    3ad2ant3
    coeq12d
    eqtr4d
    @2
    @9
    wa
    #
    @15
    @3
    cfv
    @8
    @3
    cfv
    #
    @20
    @5
    @19
    @15
    @8
    @3
    @9
    @17
    @2
    @18
    adantl
    fveq2d
    @19
    cK
    clat
    wcel
    #
    @20
    cK
    cbs
    cfv
    #
    wcel
    @20
    @20
    @5
    wbr
    @0
    @21
    @1
    @9
    cK
    hllat
    ad2antrr
    @22
    @3
    cT
    @8
    cH
    cK
    cW
    @22
    eqid
    #
    tendof.h
    tendof.t
    @7
    trlcl
    @22
    cK
    @5
    @20
    @23
    @6
    latref
    syl2anc
    eqbrtrd
    istendod
end
