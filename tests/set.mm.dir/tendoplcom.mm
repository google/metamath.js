include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "simp1.mm"
include "tendoplcl.mm"
include "3com23.mm"
include "ccom.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "tendocl.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "ltrncom.mm"
include "tendopl2.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "tendoeq1.mm"
include "syl121anc.mm"

theorem tendoplcom
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  let cG: class G
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
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
  disjoint g h
  disjoint g i
  disjoint g s
  disjoint g t
  disjoint E g
  disjoint h i
  disjoint h s
  disjoint h t
  disjoint E h
  disjoint i s
  disjoint i t
  disjoint E i
  disjoint H g
  disjoint H h
  disjoint H i
  disjoint K g
  disjoint K h
  disjoint K i
  disjoint P h
  disjoint P i
  disjoint T g
  disjoint T h
  disjoint T i
  disjoint U g
  disjoint U h
  disjoint U i
  disjoint V g
  disjoint V h
  disjoint V i
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint W g
  disjoint W h
  disjoint W i
  disjoint P g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ U e. E /\ V e. E ) -> ( U P V ) = ( V P U ) )

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
    w3a
    #
    @0
    cU
    cV
    cP
    co
    #
    cE
    wcel
    cV
    cU
    cP
    co
    #
    cE
    wcel
    #
    vg
    cv
    #
    @4
    cfv
    #
    @7
    @5
    cfv
    #
    wceq
    #
    vg
    cT
    wral
    @4
    @5
    wceq
    @0
    @1
    @2
    simp1
    vt
    cP
    cT
    cU
    vf
    cE
    cH
    cK
    cV
    cW
    vs
    tendopl.h
    tendopl.t
    tendopl.e
    tendopl.p
    tendoplcl
    @0
    @2
    @1
    @6
    vt
    cP
    cT
    cV
    vf
    cE
    cH
    cK
    cU
    cW
    vs
    tendopl.h
    tendopl.t
    tendopl.e
    tendopl.p
    tendoplcl
    3com23
    @3
    @10
    vg
    cT
    @3
    @7
    cT
    wcel
    #
    wa
    #
    @7
    cU
    cfv
    #
    @7
    cV
    cfv
    #
    ccom
    #
    @14
    @13
    ccom
    #
    @8
    @9
    @12
    @0
    @13
    cT
    wcel
    #
    @14
    cT
    wcel
    #
    @15
    @16
    wceq
    @0
    @1
    @2
    @11
    simpl1
    #
    @12
    @0
    @1
    @11
    @17
    @19
    @0
    @1
    @2
    @11
    simpl2
    #
    @3
    @11
    simpr
    #
    cU
    cT
    cE
    @7
    cH
    cK
    chlt
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendocl
    syl3anc
    @12
    @0
    @2
    @11
    @18
    @19
    @0
    @1
    @2
    @11
    simpl3
    #
    @21
    cV
    cT
    cE
    @7
    cH
    cK
    chlt
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendocl
    syl3anc
    cT
    @13
    @14
    cH
    cK
    cW
    tendopl.h
    tendopl.t
    ltrncom
    syl3anc
    @12
    @1
    @2
    @11
    @8
    @15
    wceq
    @20
    @22
    @21
    vt
    cP
    cT
    cU
    vf
    cE
    @7
    cK
    cV
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    syl3anc
    @12
    @2
    @1
    @11
    @9
    @16
    wceq
    @22
    @20
    @21
    vt
    cP
    cT
    cV
    vf
    cE
    @7
    cK
    cU
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    syl3anc
    3eqtr4d
    ralrimiva
    cT
    @4
    vg
    cE
    cH
    cK
    @5
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendoeq1
    syl121anc
end
