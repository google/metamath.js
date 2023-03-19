include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wrex.mm"
include "ccom.mm"
include "wceq.mm"
include "cdlemftr0.mm"
include "3ad2ant1.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp12r.mm"
include "simp2.mm"
include "simp3.mm"
include "simp13l.mm"
include "simp13r.mm"
include "cdleml3N.mm"
include "syl133anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem cdleml4N
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  let vf: setvar f
  assume cdleml1.b: |- B = ( Base ` K )
  assume cdleml1.h: |- H = ( LHyp ` K )
  assume cdleml1.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdleml1.r: |- R = ( ( trL ` K ) ` W )
  assume cdleml1.e: |- E = ( ( TEndo ` K ) ` W )
  assume cdleml3.o: |- .0. = ( g e. T |-> ( _I |` B ) )

  disjoint E s
  disjoint K s
  disjoint R s
  disjoint T s
  disjoint U s
  disjoint V s
  disjoint W s
  disjoint g s
  disjoint B g
  disjoint B s
  disjoint H g
  disjoint H s
  disjoint K g
  disjoint .0. s
  disjoint T g
  disjoint W g
  disjoint f s
  disjoint E f
  disjoint f g
  disjoint H f
  disjoint K f
  disjoint .0. f
  disjoint T f
  disjoint U f
  disjoint V f
  disjoint W f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E ) /\ ( U =/= .0. /\ V =/= .0. ) ) -> E. s e. E ( s o. U ) = V )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    cE
    wcel
    #
    cV
    cE
    wcel
    #
    wa
    #
    cU
    c.0
    wne
    #
    cV
    c.0
    wne
    #
    wa
    #
    w3a
    #
    vf
    cv
    #
    cid
    cB
    cres
    wne
    #
    vf
    cT
    wrex
    #
    vs
    cv
    cU
    ccom
    cV
    wceq
    vs
    cE
    wrex
    #
    @0
    @3
    @10
    @6
    cB
    cT
    vf
    cH
    cK
    cW
    cdleml1.b
    cdleml1.h
    cdleml1.t
    cdlemftr0
    3ad2ant1
    @7
    @9
    @11
    vf
    cT
    @7
    @8
    cT
    wcel
    #
    @9
    w3a
    @0
    @1
    @2
    @12
    @9
    @4
    @5
    @11
    @0
    @3
    @6
    @12
    @9
    simp11
    @1
    @2
    @0
    @6
    @12
    @9
    simp12l
    @1
    @2
    @0
    @6
    @12
    @9
    simp12r
    @7
    @12
    @9
    simp2
    @7
    @12
    @9
    simp3
    @4
    @5
    @0
    @3
    @12
    @9
    simp13l
    @4
    @5
    @0
    @3
    @12
    @9
    simp13r
    cB
    cR
    cT
    cU
    vf
    vg
    cE
    cH
    cK
    cV
    cW
    c.0
    vs
    cdleml1.b
    cdleml1.h
    cdleml1.t
    cdleml1.r
    cdleml1.e
    cdleml3.o
    cdleml3N
    syl133anc
    rexlimdv3a
    mpd
end
