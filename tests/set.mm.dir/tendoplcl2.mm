include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "tendopl2.mm"
include "3expa.mm"
include "3adant1.mm"
include "simp1.mm"
include "tendocl.mm"
include "3adant2r.mm"
include "3adant2l.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem tendoplcl2
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  assume tendopl.h: |- H = ( LHyp ` K )
  assume tendopl.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendopl.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendopl.p: |- P = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) )

  disjoint s t
  disjoint E s
  disjoint E t
  disjoint f s
  disjoint f t
  disjoint T f
  disjoint T s
  disjoint T t
  disjoint W f
  disjoint W s
  disjoint W t
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E ) /\ F e. T ) -> ( ( U P V ) ` F ) e. T )

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
    cF
    cT
    wcel
    #
    w3a
    #
    cF
    cU
    cV
    cP
    co
    cfv
    #
    cF
    cU
    cfv
    #
    cF
    cV
    cfv
    #
    ccom
    #
    cT
    @3
    @4
    @6
    @9
    wceq
    #
    @0
    @1
    @2
    @4
    @10
    vt
    cP
    cT
    cU
    vf
    cE
    cF
    cK
    cV
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    3expa
    3adant1
    @5
    @0
    @7
    cT
    wcel
    #
    @8
    cT
    wcel
    #
    @9
    cT
    wcel
    @0
    @3
    @4
    simp1
    @0
    @1
    @4
    @11
    @2
    cU
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendocl
    3adant2r
    @0
    @2
    @4
    @12
    @1
    cV
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendocl
    3adant2l
    cT
    @7
    @8
    cH
    cK
    cW
    tendopl.h
    tendopl.t
    ltrnco
    syl3anc
    eqeltrd
end
