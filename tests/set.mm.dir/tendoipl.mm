include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "simpl.mm"
include "tendoicl.mm"
include "simpr.mm"
include "tendoplcl.mm"
include "syl3anc.mm"
include "tendo0cl.mm"
include "adantr.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "ccnv.mm"
include "tendoi2.mm"
include "adantll.mm"
include "coeq1d.mm"
include "wf1o.mm"
include "simpll.mm"
include "tendocl.mm"
include "3expa.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "eqtrd.mm"
include "simplr.mm"
include "tendopl2.mm"
include "tendo02.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "tendoeq1.mm"
include "syl121anc.mm"

theorem tendoipl
  let vt: setvar t
  let cB: class B
  let cP: class P
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let cO: class O
  let cW: class W
  let vs: setvar s
  let vg: setvar g
  let vh: setvar h
  assume tendoicl.h: |- H = ( LHyp ` K )
  assume tendoicl.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendoicl.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendoicl.i: |- I = ( s e. E |-> ( f e. T |-> `' ( s ` f ) ) )
  assume tendoi.b: |- B = ( Base ` K )
  assume tendoi.p: |- P = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) )
  assume tendoi.o: |- O = ( f e. T |-> ( _I |` B ) )

  disjoint E s
  disjoint f s
  disjoint T f
  disjoint T s
  disjoint W f
  disjoint W s
  disjoint B f
  disjoint E t
  disjoint H f
  disjoint K f
  disjoint f t
  disjoint s t
  disjoint T t
  disjoint W t
  disjoint g h
  disjoint g s
  disjoint E g
  disjoint h s
  disjoint E h
  disjoint H g
  disjoint H h
  disjoint I g
  disjoint I h
  disjoint K g
  disjoint K h
  disjoint S g
  disjoint S h
  disjoint f g
  disjoint f h
  disjoint T g
  disjoint T h
  disjoint W g
  disjoint W h
  disjoint O g
  disjoint P g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ S e. E ) -> ( ( I ` S ) P S ) = O )

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
    cS
    cI
    cfv
    #
    cS
    cP
    co
    #
    cE
    wcel
    #
    cO
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
    cO
    cfv
    #
    wceq
    #
    vg
    cT
    wral
    @4
    cO
    wceq
    @0
    @1
    simpl
    #
    @2
    @0
    @3
    cE
    wcel
    #
    @1
    @5
    @11
    cS
    cT
    vf
    cE
    cH
    cI
    cK
    cW
    vs
    tendoicl.h
    tendoicl.t
    tendoicl.e
    tendoicl.i
    tendoicl
    #
    @0
    @1
    simpr
    vt
    cP
    cT
    @3
    vf
    cE
    cH
    cK
    cS
    cW
    vs
    tendoicl.h
    tendoicl.t
    tendoicl.e
    tendoi.p
    tendoplcl
    syl3anc
    @0
    @6
    @1
    cB
    cT
    vf
    cE
    cH
    cK
    cO
    cW
    tendoi.b
    tendoicl.h
    tendoicl.t
    tendoicl.e
    tendoi.o
    tendo0cl
    adantr
    @2
    @10
    vg
    cT
    @2
    @7
    cT
    wcel
    #
    wa
    #
    @7
    @3
    cfv
    #
    @7
    cS
    cfv
    #
    ccom
    #
    cid
    cB
    cres
    #
    @8
    @9
    @15
    @18
    @17
    ccnv
    #
    @17
    ccom
    #
    @19
    @15
    @16
    @20
    @17
    @1
    @14
    @16
    @20
    wceq
    @0
    cS
    cT
    vf
    cE
    @7
    cI
    cK
    cW
    vs
    tendoicl.i
    tendoicl.t
    tendoi2
    adantll
    coeq1d
    @15
    cB
    cB
    @17
    wf1o
    #
    @21
    @19
    wceq
    @15
    @0
    @17
    cT
    wcel
    #
    @22
    @0
    @1
    @14
    simpll
    @0
    @1
    @14
    @23
    cS
    cT
    cE
    @7
    cH
    cK
    chlt
    cW
    tendoicl.h
    tendoicl.t
    tendoicl.e
    tendocl
    3expa
    cB
    cT
    @17
    cH
    cK
    chlt
    cW
    tendoi.b
    tendoicl.h
    tendoicl.t
    ltrn1o
    syl2anc
    cB
    cB
    @17
    f1ococnv1
    syl
    eqtrd
    @15
    @12
    @1
    @14
    @8
    @18
    wceq
    @2
    @12
    @14
    @13
    adantr
    @0
    @1
    @14
    simplr
    @2
    @14
    simpr
    vt
    cP
    cT
    @3
    vf
    cE
    @7
    cK
    cS
    cW
    vs
    tendoi.p
    tendoicl.t
    tendopl2
    syl3anc
    @14
    @9
    @19
    wceq
    @2
    cB
    cT
    vf
    @7
    cK
    cO
    tendoi.o
    tendoi.b
    tendo02
    adantl
    3eqtr4d
    ralrimiva
    cT
    @4
    vg
    cE
    cH
    cK
    cO
    cW
    tendoicl.h
    tendoicl.t
    tendoicl.e
    tendoeq1
    syl121anc
end
