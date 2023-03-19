include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "simpl.mm"
include "tendo0cl.mm"
include "adantr.mm"
include "simpr.mm"
include "tendoplcl.mm"
include "syl3anc.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "simpll.mm"
include "syl.mm"
include "simplr.mm"
include "tendopl2.mm"
include "tendo02.mm"
include "adantl.mm"
include "coeq1d.mm"
include "wf1o.mm"
include "wf.mm"
include "tendocl.mm"
include "3expa.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "3eqtrd.mm"
include "ralrimiva.mm"
include "tendoeq1.mm"
include "syl121anc.mm"

theorem tendo0pl
  let vt: setvar t
  let cB: class B
  let cP: class P
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let vs: setvar s
  let vg: setvar g
  let vh: setvar h
  assume tendo0.b: |- B = ( Base ` K )
  assume tendo0.h: |- H = ( LHyp ` K )
  assume tendo0.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendo0.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendo0.o: |- O = ( f e. T |-> ( _I |` B ) )
  assume tendo0pl.p: |- P = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) )

  disjoint B f
  disjoint T f
  disjoint s t
  disjoint E s
  disjoint E t
  disjoint T s
  disjoint T t
  disjoint f s
  disjoint f t
  disjoint W f
  disjoint W s
  disjoint W t
  disjoint B g
  disjoint g h
  disjoint H g
  disjoint H h
  disjoint K g
  disjoint K h
  disjoint O g
  disjoint O h
  disjoint T g
  disjoint T h
  disjoint W g
  disjoint W h
  disjoint g s
  disjoint g t
  disjoint E g
  disjoint P g
  disjoint S g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ S e. E ) -> ( O P S ) = S )

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
    wa
    #
    @0
    cO
    cS
    cP
    co
    #
    cE
    wcel
    #
    @1
    vg
    cv
    #
    @3
    cfv
    #
    @5
    cS
    cfv
    #
    wceq
    #
    vg
    cT
    wral
    @3
    cS
    wceq
    @0
    @1
    simpl
    #
    @2
    @0
    cO
    cE
    wcel
    #
    @1
    @4
    @9
    @0
    @10
    @1
    cB
    cT
    vf
    cE
    cH
    cK
    cO
    cW
    tendo0.b
    tendo0.h
    tendo0.t
    tendo0.e
    tendo0.o
    tendo0cl
    #
    adantr
    @0
    @1
    simpr
    #
    vt
    cP
    cT
    cO
    vf
    cE
    cH
    cK
    cS
    cW
    vs
    tendo0.h
    tendo0.t
    tendo0.e
    tendo0pl.p
    tendoplcl
    syl3anc
    @12
    @2
    @8
    vg
    cT
    @2
    @5
    cT
    wcel
    #
    wa
    #
    @6
    @5
    cO
    cfv
    #
    @7
    ccom
    #
    cid
    cB
    cres
    #
    @7
    ccom
    #
    @7
    @14
    @10
    @1
    @13
    @6
    @16
    wceq
    @14
    @0
    @10
    @0
    @1
    @13
    simpll
    #
    @11
    syl
    @0
    @1
    @13
    simplr
    @2
    @13
    simpr
    vt
    cP
    cT
    cO
    vf
    cE
    @5
    cK
    cS
    cW
    vs
    tendo0pl.p
    tendo0.t
    tendopl2
    syl3anc
    @14
    @15
    @17
    @7
    @13
    @15
    @17
    wceq
    @2
    cB
    cT
    vf
    @5
    cK
    cO
    tendo0.o
    tendo0.b
    tendo02
    adantl
    coeq1d
    @14
    cB
    cB
    @7
    wf1o
    #
    cB
    cB
    @7
    wf
    @18
    @7
    wceq
    @14
    @0
    @7
    cT
    wcel
    #
    @20
    @19
    @0
    @1
    @13
    @21
    cS
    cT
    cE
    @5
    cH
    cK
    chlt
    cW
    tendo0.h
    tendo0.t
    tendo0.e
    tendocl
    3expa
    cB
    cT
    @7
    cH
    cK
    chlt
    cW
    tendo0.b
    tendo0.h
    tendo0.t
    ltrn1o
    syl2anc
    cB
    cB
    @7
    f1of
    cB
    cB
    @7
    fcoi2
    3syl
    3eqtrd
    ralrimiva
    cT
    @3
    vg
    cE
    cH
    cK
    cS
    cW
    tendo0.h
    tendo0.t
    tendo0.e
    tendoeq1
    syl121anc
end
