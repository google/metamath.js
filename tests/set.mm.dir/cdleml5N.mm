include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl1.mm"
include "tendo0cl.mm"
include "syl.mm"
include "simpl2l.mm"
include "tendo0mul.mm"
include "syl2anc.mm"
include "simpr.mm"
include "eqtr4d.mm"
include "coeq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "simpl2.mm"
include "simpl3.mm"
include "cdleml4N.mm"
include "syl112anc.mm"
include "pm2.61dane.mm"

theorem cdleml5N
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E ) /\ U =/= .0. ) -> E. s e. E ( s o. U ) = V )

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
    w3a
    #
    vs
    cv
    #
    cU
    ccom
    #
    cV
    wceq
    #
    vs
    cE
    wrex
    #
    cV
    c.0
    @5
    cV
    c.0
    wceq
    #
    wa
    #
    c.0
    cE
    wcel
    #
    c.0
    cU
    ccom
    #
    cV
    wceq
    #
    @9
    @11
    @0
    @12
    @0
    @3
    @4
    @10
    simpl1
    #
    cB
    cT
    vg
    cE
    cH
    cK
    c.0
    cW
    cdleml1.b
    cdleml1.h
    cdleml1.t
    cdleml1.e
    cdleml3.o
    tendo0cl
    syl
    @11
    @13
    c.0
    cV
    @11
    @0
    @1
    @13
    c.0
    wceq
    @15
    @1
    @2
    @0
    @4
    @10
    simpl2l
    cB
    cT
    cU
    vg
    cE
    cH
    cK
    c.0
    cW
    cdleml1.b
    cdleml1.h
    cdleml1.t
    cdleml1.e
    cdleml3.o
    tendo0mul
    syl2anc
    @5
    @10
    simpr
    eqtr4d
    @8
    @14
    vs
    c.0
    cE
    @6
    c.0
    wceq
    @7
    @13
    cV
    @6
    c.0
    cU
    coeq1
    eqeq1d
    rspcev
    syl2anc
    @5
    cV
    c.0
    wne
    #
    wa
    @0
    @3
    @4
    @16
    @9
    @0
    @3
    @4
    @16
    simpl1
    @0
    @3
    @4
    @16
    simpl2
    @0
    @3
    @4
    @16
    simpl3
    @5
    @16
    simpr
    cB
    cR
    cT
    cU
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
    cdleml4N
    syl112anc
    pm2.61dane
end
