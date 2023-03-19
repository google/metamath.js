include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "ccom.mm"
include "cfv.mm"
include "co.mm"
include "tendoco2.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp3r.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3.mm"
include "tendopl2.mm"
include "syld3an3.mm"
include "coeq12d.mm"
include "3eqtr4d.mm"

theorem tendoplco2
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cG: class G
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
  disjoint G f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E ) /\ ( F e. T /\ G e. T ) ) -> ( ( U P V ) ` ( F o. G ) ) = ( ( ( U P V ) ` F ) o. ( ( U P V ) ` G ) ) )

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
    cG
    cT
    wcel
    #
    wa
    #
    w3a
    #
    cF
    cG
    ccom
    #
    cU
    cfv
    @8
    cV
    cfv
    ccom
    #
    cF
    cU
    cfv
    cF
    cV
    cfv
    ccom
    #
    cG
    cU
    cfv
    cG
    cV
    cfv
    ccom
    #
    ccom
    @8
    cU
    cV
    cP
    co
    #
    cfv
    #
    cF
    @12
    cfv
    #
    cG
    @12
    cfv
    #
    ccom
    cT
    cU
    cE
    cF
    cG
    cH
    cK
    cV
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendoco2
    @0
    @3
    @6
    @8
    cT
    wcel
    #
    @13
    @9
    wceq
    #
    @7
    @0
    @4
    @5
    @16
    @0
    @3
    @6
    simp1
    @0
    @3
    @4
    @5
    simp3l
    #
    @0
    @3
    @4
    @5
    simp3r
    #
    cT
    cF
    cG
    cH
    cK
    cW
    tendopl.h
    tendopl.t
    ltrnco
    syl3anc
    @0
    @3
    @16
    w3a
    @1
    @2
    @16
    @17
    @0
    @1
    @2
    @16
    simp2l
    @0
    @1
    @2
    @16
    simp2r
    @0
    @3
    @16
    simp3
    vt
    cP
    cT
    cU
    vf
    cE
    @8
    cK
    cV
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    syl3anc
    syld3an3
    @7
    @14
    @10
    @15
    @11
    @7
    @1
    @2
    @4
    @14
    @10
    wceq
    @0
    @1
    @2
    @6
    simp2l
    #
    @0
    @1
    @2
    @6
    simp2r
    #
    @18
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
    syl3anc
    @7
    @1
    @2
    @5
    @15
    @11
    wceq
    @20
    @21
    @19
    vt
    cP
    cT
    cU
    vf
    cE
    cG
    cK
    cV
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    syl3anc
    coeq12d
    3eqtr4d
end
