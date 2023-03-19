include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "ccom.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "tendoplcl.mm"
include "syl3anc.mm"
include "tendococl.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplr1.mm"
include "simpll.mm"
include "simplr2.mm"
include "simpr.mm"
include "tendocl.mm"
include "simplr3.mm"
include "tendovalco.mm"
include "syl32anc.mm"
include "tendopl2.mm"
include "fveq2d.mm"
include "tendocoval.mm"
include "syl221anc.mm"
include "coeq12d.mm"
include "3eqtr4rd.mm"
include "syl121anc.mm"
include "ralrimiva.mm"
include "tendoeq1.mm"

theorem tendodi1
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S e. E /\ U e. E /\ V e. E ) ) -> ( S o. ( U P V ) ) = ( ( S o. U ) P ( S o. V ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
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
    @2
    cS
    cU
    cV
    cP
    co
    #
    ccom
    #
    cE
    wcel
    #
    cS
    cU
    ccom
    #
    cS
    cV
    ccom
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
    @9
    cfv
    #
    @15
    @13
    cfv
    #
    wceq
    #
    vg
    cT
    wral
    @9
    @13
    wceq
    @2
    @6
    simpl
    #
    @7
    @2
    @3
    @8
    cE
    wcel
    #
    @10
    @19
    @2
    @3
    @4
    @5
    simpr1
    #
    @7
    @2
    @4
    @5
    @20
    @19
    @2
    @3
    @4
    @5
    simpr2
    #
    @2
    @3
    @4
    @5
    simpr3
    #
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
    #
    syl3anc
    cS
    @8
    cE
    cH
    cK
    cW
    tendopl.h
    tendopl.e
    tendococl
    syl3anc
    @7
    @2
    @11
    cE
    wcel
    #
    @12
    cE
    wcel
    #
    @14
    @19
    @7
    @2
    @3
    @4
    @25
    @19
    @21
    @22
    cS
    cU
    cE
    cH
    cK
    cW
    tendopl.h
    tendopl.e
    tendococl
    #
    syl3anc
    @7
    @2
    @3
    @5
    @26
    @19
    @21
    @23
    cS
    cV
    cE
    cH
    cK
    cW
    tendopl.h
    tendopl.e
    tendococl
    #
    syl3anc
    vt
    cP
    cT
    @11
    vf
    cE
    cH
    cK
    @12
    cW
    vs
    tendopl.h
    tendopl.t
    tendopl.e
    tendopl.p
    tendoplcl
    syl3anc
    @7
    @18
    vg
    cT
    @7
    @15
    cT
    wcel
    #
    wa
    #
    @15
    @11
    cfv
    #
    @15
    @12
    cfv
    #
    ccom
    #
    @15
    @8
    cfv
    #
    cS
    cfv
    #
    @17
    @16
    @30
    @15
    cU
    cfv
    #
    @15
    cV
    cfv
    #
    ccom
    #
    cS
    cfv
    #
    @36
    cS
    cfv
    #
    @37
    cS
    cfv
    #
    ccom
    #
    @35
    @33
    @30
    @0
    @1
    @3
    @36
    cT
    wcel
    #
    @37
    cT
    wcel
    #
    @39
    @42
    wceq
    @0
    @1
    @6
    @29
    simplll
    #
    @0
    @1
    @6
    @29
    simpllr
    #
    @3
    @4
    @5
    @2
    @29
    simplr1
    #
    @30
    @2
    @4
    @29
    @43
    @2
    @6
    @29
    simpll
    #
    @3
    @4
    @5
    @2
    @29
    simplr2
    #
    @7
    @29
    simpr
    #
    cU
    cT
    cE
    @15
    cH
    cK
    chlt
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendocl
    syl3anc
    @30
    @2
    @5
    @29
    @44
    @48
    @3
    @4
    @5
    @2
    @29
    simplr3
    #
    @50
    cV
    cT
    cE
    @15
    cH
    cK
    chlt
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendocl
    syl3anc
    cS
    cT
    cE
    @36
    @37
    cH
    cK
    chlt
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendovalco
    syl32anc
    @30
    @34
    @38
    cS
    @30
    @4
    @5
    @29
    @34
    @38
    wceq
    @49
    @51
    @50
    vt
    cP
    cT
    cU
    vf
    cE
    @15
    cK
    cV
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    syl3anc
    fveq2d
    @30
    @31
    @40
    @32
    @41
    @30
    @0
    @1
    @3
    @4
    @29
    @31
    @40
    wceq
    @45
    @46
    @47
    @49
    @50
    cT
    cS
    cE
    @15
    cH
    cK
    cU
    cW
    chlt
    tendopl.h
    tendopl.t
    tendopl.e
    tendocoval
    syl221anc
    @30
    @0
    @1
    @3
    @5
    @29
    @32
    @41
    wceq
    @45
    @46
    @47
    @51
    @50
    cT
    cS
    cE
    @15
    cH
    cK
    cV
    cW
    chlt
    tendopl.h
    tendopl.t
    tendopl.e
    tendocoval
    syl221anc
    coeq12d
    3eqtr4rd
    @30
    @25
    @26
    @29
    @17
    @33
    wceq
    @30
    @2
    @3
    @4
    @25
    @48
    @47
    @49
    @27
    syl3anc
    @30
    @2
    @3
    @5
    @26
    @48
    @47
    @51
    @28
    syl3anc
    @50
    vt
    cP
    cT
    @11
    vf
    cE
    @15
    cK
    @12
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    syl3anc
    @30
    @2
    @3
    @20
    @29
    @16
    @35
    wceq
    @48
    @47
    @30
    @2
    @4
    @5
    @20
    @48
    @49
    @51
    @24
    syl3anc
    @50
    cT
    cS
    cE
    @15
    cH
    cK
    @8
    cW
    chlt
    tendopl.h
    tendopl.t
    tendopl.e
    tendocoval
    syl121anc
    3eqtr4rd
    ralrimiva
    cT
    @9
    vg
    cE
    cH
    cK
    @13
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendoeq1
    syl121anc
end
