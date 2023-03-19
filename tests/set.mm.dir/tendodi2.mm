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
include "tendoplcl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "tendococl.mm"
include "simpll.mm"
include "simplr1.mm"
include "simplr2.mm"
include "simplr3.mm"
include "simpr.mm"
include "tendocoval.mm"
include "syl121anc.mm"
include "simplll.mm"
include "simpllr.mm"
include "syl221anc.mm"
include "coeq12d.mm"
include "tendopl2.mm"
include "tendocl.mm"
include "3eqtr4rd.mm"
include "eqtrd.mm"
include "ralrimiva.mm"
include "tendoeq1.mm"

theorem tendodi2
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S e. E /\ U e. E /\ V e. E ) ) -> ( ( S P U ) o. V ) = ( ( S o. V ) P ( U o. V ) ) )

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
    cP
    co
    #
    cV
    ccom
    #
    cE
    wcel
    #
    cS
    cV
    ccom
    #
    cU
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
    @8
    cE
    wcel
    #
    @5
    @10
    @19
    @7
    @2
    @3
    @4
    @20
    @19
    @2
    @3
    @4
    @5
    simpr1
    #
    @2
    @3
    @4
    @5
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
    #
    syl3anc
    @2
    @3
    @4
    @5
    simpr3
    #
    @8
    cV
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
    @5
    @25
    @19
    @21
    @24
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
    @7
    @2
    @4
    @5
    @26
    @19
    @22
    @24
    cU
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
    @16
    @15
    cV
    cfv
    #
    @8
    cfv
    #
    @17
    @30
    @2
    @20
    @5
    @29
    @16
    @32
    wceq
    @2
    @6
    @29
    simpll
    #
    @30
    @2
    @3
    @4
    @20
    @33
    @3
    @4
    @5
    @2
    @29
    simplr1
    #
    @3
    @4
    @5
    @2
    @29
    simplr2
    #
    @23
    syl3anc
    @3
    @4
    @5
    @2
    @29
    simplr3
    #
    @7
    @29
    simpr
    #
    cT
    @8
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
    syl121anc
    @30
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
    @31
    cS
    cfv
    #
    @31
    cU
    cfv
    #
    ccom
    #
    @17
    @32
    @30
    @38
    @41
    @39
    @42
    @30
    @0
    @1
    @3
    @5
    @29
    @38
    @41
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
    @34
    @36
    @37
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
    @30
    @0
    @1
    @4
    @5
    @29
    @39
    @42
    wceq
    @44
    @45
    @35
    @36
    @37
    cT
    cU
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
    @30
    @25
    @26
    @29
    @17
    @40
    wceq
    @30
    @2
    @3
    @5
    @25
    @33
    @34
    @36
    @27
    syl3anc
    @30
    @2
    @4
    @5
    @26
    @33
    @35
    @36
    @28
    syl3anc
    @37
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
    @3
    @4
    @31
    cT
    wcel
    #
    @32
    @43
    wceq
    @34
    @35
    @30
    @2
    @5
    @29
    @46
    @33
    @36
    @37
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
    vt
    cP
    cT
    cS
    vf
    cE
    @31
    cK
    cU
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    syl3anc
    3eqtr4rd
    eqtrd
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
