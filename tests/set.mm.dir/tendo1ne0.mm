include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "wrex.mm"
include "cdlemftr0.mm"
include "w3a.mm"
include "simp3.mm"
include "wceq.mm"
include "cfv.mm"
include "fveq1.mm"
include "adantl.mm"
include "simpl2.mm"
include "fvresi.mm"
include "syl.mm"
include "tendo02.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"
include "rexlimdv3a.mm"

theorem tendo1ne0
  let cB: class B
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let vg: setvar g
  let cU: class U
  let cV: class V
  assume tendoid0.b: |- B = ( Base ` K )
  assume tendoid0.h: |- H = ( LHyp ` K )
  assume tendoid0.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendoid0.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendoid0.o: |- O = ( f e. T |-> ( _I |` B ) )

  disjoint B f
  disjoint T f
  disjoint f g
  disjoint B g
  disjoint H g
  disjoint K g
  disjoint T g
  disjoint W g
  disjoint E g
  disjoint O g
  disjoint U g
  disjoint V g
  assert |- ( ( K e. HL /\ W e. H ) -> ( _I |` T ) =/= O )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vg
    cv
    #
    cid
    cB
    cres
    #
    wne
    #
    vg
    cT
    wrex
    cid
    cT
    cres
    #
    cO
    wne
    #
    cB
    cT
    vg
    cH
    cK
    cW
    tendoid0.b
    tendoid0.h
    tendoid0.t
    cdlemftr0
    @0
    @3
    @5
    vg
    cT
    @0
    @1
    cT
    wcel
    #
    @3
    w3a
    #
    @3
    @5
    @0
    @6
    @3
    simp3
    @7
    @4
    cO
    @1
    @2
    @7
    @4
    cO
    wceq
    #
    @1
    @2
    wceq
    @7
    @8
    wa
    #
    @1
    @4
    cfv
    #
    @1
    cO
    cfv
    #
    @1
    @2
    @8
    @10
    @11
    wceq
    @7
    @1
    @4
    cO
    fveq1
    adantl
    @9
    @6
    @10
    @1
    wceq
    @0
    @6
    @3
    @8
    simpl2
    #
    cT
    @1
    fvresi
    syl
    @9
    @6
    @11
    @2
    wceq
    @12
    cB
    cT
    vf
    @1
    cK
    cO
    tendoid0.o
    tendoid0.b
    tendo02
    syl
    3eqtr3d
    ex
    necon3d
    mpd
    rexlimdv3a
    mpd
end
