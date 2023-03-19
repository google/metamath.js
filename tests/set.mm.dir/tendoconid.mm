include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "ccom.mm"
include "wrex.mm"
include "cdlemftr0.mm"
include "3ad2ant1.mm"
include "cfv.mm"
include "wf.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl3l.mm"
include "tendof.mm"
include "syl2anc.mm"
include "simprl.mm"
include "fvco3.mm"
include "simpl2r.mm"
include "wb.mm"
include "simpl2l.mm"
include "tendocl.mm"
include "syl3anc.mm"
include "simpl3r.mm"
include "simpr.mm"
include "tendoid0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "syl112anc.mm"
include "eqnetrd.mm"
include "tendococl.mm"
include "mpbid.mm"
include "rexlimddv.mm"

theorem tendoconid
  let cB: class B
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cO: class O
  let cV: class V
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
  disjoint E g
  disjoint O g
  disjoint U g
  disjoint V g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ U =/= O ) /\ ( V e. E /\ V =/= O ) ) -> ( U o. V ) =/= O )

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
    cU
    cO
    wne
    #
    wa
    #
    cV
    cE
    wcel
    #
    cV
    cO
    wne
    #
    wa
    #
    w3a
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
    cU
    cV
    ccom
    #
    cO
    wne
    #
    vg
    cT
    @0
    @3
    @10
    vg
    cT
    wrex
    @6
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
    3ad2ant1
    @7
    @8
    cT
    wcel
    #
    @10
    wa
    #
    wa
    #
    @8
    @11
    cfv
    #
    @9
    wne
    @12
    @15
    @16
    @8
    cV
    cfv
    #
    cU
    cfv
    #
    @9
    @15
    cT
    cT
    cV
    wf
    #
    @13
    @16
    @18
    wceq
    @15
    @0
    @4
    @19
    @0
    @3
    @6
    @14
    simpl1
    #
    @4
    @5
    @0
    @3
    @14
    simpl3l
    #
    cV
    cT
    cE
    cH
    cK
    chlt
    cW
    tendoid0.h
    tendoid0.t
    tendoid0.e
    tendof
    syl2anc
    @7
    @13
    @10
    simprl
    #
    cT
    cT
    @8
    cU
    cV
    fvco3
    syl2anc
    @15
    @18
    @9
    wne
    @2
    @1
    @2
    @0
    @6
    @14
    simpl2r
    @15
    @18
    @9
    cU
    cO
    @15
    @0
    @1
    @17
    cT
    wcel
    #
    @17
    @9
    wne
    #
    @18
    @9
    wceq
    cU
    cO
    wceq
    wb
    @20
    @1
    @2
    @0
    @6
    @14
    simpl2l
    #
    @15
    @0
    @4
    @13
    @23
    @20
    @21
    @22
    cV
    cT
    cE
    @8
    cH
    cK
    chlt
    cW
    tendoid0.h
    tendoid0.t
    tendoid0.e
    tendocl
    syl3anc
    @15
    @24
    @5
    @4
    @5
    @0
    @3
    @14
    simpl3r
    @15
    @17
    @9
    cV
    cO
    @15
    @0
    @4
    @14
    @17
    @9
    wceq
    cV
    cO
    wceq
    wb
    @20
    @21
    @7
    @14
    simpr
    #
    cB
    cT
    cV
    vf
    cE
    @8
    cH
    cK
    cO
    cW
    tendoid0.b
    tendoid0.h
    tendoid0.t
    tendoid0.e
    tendoid0.o
    tendoid0
    syl3anc
    necon3bid
    mpbird
    cB
    cT
    cU
    vf
    cE
    @17
    cH
    cK
    cO
    cW
    tendoid0.b
    tendoid0.h
    tendoid0.t
    tendoid0.e
    tendoid0.o
    tendoid0
    syl112anc
    necon3bid
    mpbird
    eqnetrd
    @15
    @16
    @9
    @11
    cO
    @15
    @0
    @11
    cE
    wcel
    #
    @14
    @16
    @9
    wceq
    @11
    cO
    wceq
    wb
    @20
    @15
    @0
    @1
    @4
    @27
    @20
    @25
    @21
    cU
    cV
    cE
    cH
    cK
    cW
    tendoid0.h
    tendoid0.e
    tendococl
    syl3anc
    @26
    cB
    cT
    @11
    vf
    cE
    @8
    cH
    cK
    cO
    cW
    tendoid0.b
    tendoid0.h
    tendoid0.t
    tendoid0.e
    tendoid0.o
    tendoid0
    syl3anc
    necon3bid
    mpbid
    rexlimddv
end
