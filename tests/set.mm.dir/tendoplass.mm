include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "tendoplcl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "ccom.mm"
include "coass.mm"
include "simplr1.mm"
include "simplr2.mm"
include "simpr.mm"
include "tendopl2.mm"
include "coeq1d.mm"
include "simplr3.mm"
include "coeq2d.mm"
include "3eqtr4a.mm"
include "adantr.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "tendoeq1.mm"
include "syl121anc.mm"

theorem tendoplass
  let vt: setvar t
  let cP: class P
  let cS: class S
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
  disjoint S g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S e. E /\ U e. E /\ V e. E ) ) -> ( ( S P U ) P V ) = ( S P ( U P V ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cS
    cE
    wcel
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
    wa
    #
    @0
    cS
    cU
    cP
    co
    #
    cV
    cP
    co
    #
    cE
    wcel
    #
    cS
    cU
    cV
    cP
    co
    #
    cP
    co
    #
    cE
    wcel
    #
    vg
    cv
    #
    @7
    cfv
    #
    @12
    @10
    cfv
    #
    wceq
    #
    vg
    cT
    wral
    @7
    @10
    wceq
    @0
    @4
    simpl
    #
    @5
    @0
    @6
    cE
    wcel
    #
    @3
    @8
    @16
    @5
    @0
    @1
    @2
    @17
    @16
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    vt
    cP
    cT
    cS
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
    syl3anc
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    vt
    cP
    cT
    @6
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
    syl3anc
    @5
    @0
    @1
    @9
    cE
    wcel
    #
    @11
    @16
    @18
    @5
    @0
    @2
    @3
    @22
    @16
    @19
    @21
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
    syl3anc
    #
    vt
    cP
    cT
    cS
    vf
    cE
    cH
    cK
    @9
    cW
    vs
    tendopl.h
    tendopl.t
    tendopl.e
    tendopl.p
    tendoplcl
    syl3anc
    @5
    @15
    vg
    cT
    @5
    @12
    cT
    wcel
    #
    wa
    #
    @12
    @6
    cfv
    #
    @12
    cV
    cfv
    #
    ccom
    #
    @12
    cS
    cfv
    #
    @12
    @9
    cfv
    #
    ccom
    #
    @13
    @14
    @25
    @29
    @12
    cU
    cfv
    #
    ccom
    #
    @27
    ccom
    @29
    @32
    @27
    ccom
    #
    ccom
    @28
    @31
    @29
    @32
    @27
    coass
    @25
    @26
    @33
    @27
    @25
    @1
    @2
    @24
    @26
    @33
    wceq
    @1
    @2
    @3
    @0
    @24
    simplr1
    #
    @1
    @2
    @3
    @0
    @24
    simplr2
    #
    @5
    @24
    simpr
    #
    vt
    cP
    cT
    cS
    vf
    cE
    @12
    cK
    cU
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    syl3anc
    coeq1d
    @25
    @30
    @34
    @29
    @25
    @2
    @3
    @24
    @30
    @34
    wceq
    @36
    @1
    @2
    @3
    @0
    @24
    simplr3
    #
    @37
    vt
    cP
    cT
    cU
    vf
    cE
    @12
    cK
    cV
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    syl3anc
    coeq2d
    3eqtr4a
    @25
    @17
    @3
    @24
    @13
    @28
    wceq
    @5
    @17
    @24
    @20
    adantr
    @38
    @37
    vt
    cP
    cT
    @6
    vf
    cE
    @12
    cK
    cV
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    syl3anc
    @25
    @1
    @22
    @24
    @14
    @31
    wceq
    @35
    @5
    @22
    @24
    @23
    adantr
    @37
    vt
    cP
    cT
    cS
    vf
    cE
    @12
    cK
    @9
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    syl3anc
    3eqtr4d
    ralrimiva
    cT
    @7
    vg
    cE
    cH
    cK
    @10
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendoeq1
    syl121anc
end
