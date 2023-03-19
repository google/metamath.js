include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "ctrl.mm"
include "cfv.mm"
include "co.mm"
include "cple.mm"
include "eqid.mm"
include "simp1.mm"
include "wf.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "tendocl.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "ltrnco.mm"
include "fmptd.mm"
include "wceq.mm"
include "tendopl.mm"
include "3adant1.mm"
include "feq1d.mm"
include "mpbird.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "3simpc.mm"
include "tendoplco2.mm"
include "syl121anc.mm"
include "wbr.mm"
include "tendopltp.mm"
include "istendod.mm"

theorem tendoplcl
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ U e. E /\ V e. E ) -> ( U P V ) e. E )

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
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cU
    cV
    cP
    co
    #
    cT
    vh
    vi
    cE
    cH
    cK
    cK
    cple
    cfv
    #
    chlt
    cW
    @6
    eqid
    #
    tendopl.h
    tendopl.t
    @4
    eqid
    #
    tendopl.e
    @0
    @1
    @2
    simp1
    @3
    cT
    cT
    @5
    wf
    cT
    cT
    vg
    cT
    vg
    cv
    #
    cU
    cfv
    #
    @9
    cV
    cfv
    #
    ccom
    #
    cmpt
    #
    wf
    @3
    vg
    cT
    @12
    cT
    @13
    @3
    @9
    cT
    wcel
    #
    wa
    #
    @0
    @10
    cT
    wcel
    #
    @11
    cT
    wcel
    #
    @12
    cT
    wcel
    @0
    @1
    @2
    @14
    simpl1
    #
    @15
    @0
    @1
    @14
    @16
    @18
    @0
    @1
    @2
    @14
    simpl2
    @3
    @14
    simpr
    #
    cU
    cT
    cE
    @9
    cH
    cK
    chlt
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendocl
    syl3anc
    @15
    @0
    @2
    @14
    @17
    @18
    @0
    @1
    @2
    @14
    simpl3
    @19
    cV
    cT
    cE
    @9
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
    @10
    @11
    cH
    cK
    cW
    tendopl.h
    tendopl.t
    ltrnco
    syl3anc
    @13
    eqid
    fmptd
    @3
    cT
    cT
    @5
    @13
    @1
    @2
    @5
    @13
    wceq
    @0
    vt
    cP
    cT
    cU
    vf
    vg
    cE
    cK
    cV
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl
    3adant1
    feq1d
    mpbird
    @3
    vh
    cv
    #
    cT
    wcel
    #
    vi
    cv
    #
    cT
    wcel
    #
    w3a
    @0
    @1
    @2
    @21
    @23
    wa
    @20
    @22
    ccom
    @5
    cfv
    @20
    @5
    cfv
    #
    @22
    @5
    cfv
    ccom
    wceq
    @0
    @1
    @2
    @21
    @23
    simp11
    @0
    @1
    @2
    @21
    @23
    simp12
    @0
    @1
    @2
    @21
    @23
    simp13
    @3
    @21
    @23
    3simpc
    vt
    cP
    cT
    cU
    vf
    cE
    @20
    @22
    cH
    cK
    cV
    cW
    vs
    tendopl.h
    tendopl.t
    tendopl.e
    tendopl.p
    tendoplco2
    syl121anc
    @3
    @21
    wa
    @0
    @1
    @2
    @21
    @24
    @4
    cfv
    @20
    @4
    cfv
    @6
    wbr
    @0
    @1
    @2
    @21
    simpl1
    @0
    @1
    @2
    @21
    simpl2
    @0
    @1
    @2
    @21
    simpl3
    @3
    @21
    simpr
    vt
    cP
    @4
    cT
    cU
    vf
    cE
    @20
    cH
    cK
    @6
    cV
    cW
    vs
    tendopl.h
    tendopl.t
    tendopl.e
    tendopl.p
    @7
    @8
    tendopltp
    syl121anc
    istendod
end
