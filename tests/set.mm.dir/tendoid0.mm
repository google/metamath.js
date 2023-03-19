include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "simp3l.mm"
include "tendo02.mm"
include "syl.mm"
include "eqeq2d.mm"
include "simpl1.mm"
include "simpl2.mm"
include "tendo0cl.mm"
include "simpr.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "tendocan.mm"
include "syl132anc.mm"
include "ex.mm"
include "sylbird.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem tendoid0
  let cB: class B
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let vg: setvar g
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ U e. E /\ ( F e. T /\ F =/= ( _I |` B ) ) ) -> ( ( U ` F ) = ( _I |` B ) <-> U = O ) )

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
    cF
    cT
    wcel
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    wa
    #
    w3a
    #
    cF
    cU
    cfv
    #
    @3
    wceq
    #
    cU
    cO
    wceq
    #
    @6
    @8
    @7
    cF
    cO
    cfv
    #
    wceq
    #
    @9
    @6
    @10
    @3
    @7
    @6
    @2
    @10
    @3
    wceq
    #
    @0
    @1
    @2
    @4
    simp3l
    cB
    cT
    vf
    cF
    cK
    cO
    tendoid0.o
    tendoid0.b
    tendo02
    syl
    #
    eqeq2d
    @6
    @11
    @9
    @6
    @11
    wa
    #
    @0
    @1
    cO
    cE
    wcel
    #
    @11
    @2
    @4
    @9
    @0
    @1
    @5
    @11
    simpl1
    #
    @0
    @1
    @5
    @11
    simpl2
    @14
    @0
    @15
    @16
    cB
    cT
    vf
    cE
    cH
    cK
    cO
    cW
    tendoid0.b
    tendoid0.h
    tendoid0.t
    tendoid0.e
    tendoid0.o
    tendo0cl
    syl
    @6
    @11
    simpr
    @2
    @4
    @0
    @1
    @11
    simpl3l
    @2
    @4
    @0
    @1
    @11
    simpl3r
    cB
    cT
    cU
    cE
    cF
    cH
    cK
    cO
    cW
    tendoid0.b
    tendoid0.h
    tendoid0.t
    tendoid0.e
    tendocan
    syl132anc
    ex
    sylbird
    @6
    @8
    @9
    @12
    @13
    @9
    @7
    @10
    @3
    cF
    cU
    cO
    fveq1
    eqeq1d
    syl5ibrcom
    impbid
end
