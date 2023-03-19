include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cid.mm"
include "cres.mm"
include "co.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "simprr.mm"
include "idltrn.mm"
include "adantr.mm"
include "tendoidcl.mm"
include "dvhopspN.mm"
include "syl12anc.mm"
include "tendoid.mm"
include "adantrl.mm"
include "tendo1mulr.mm"
include "opeq12d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "simprl.mm"
include "tendo0cl.mm"
include "dvhopaddN.mm"
include "syl22anc.mm"
include "wf1o.mm"
include "wf.mm"
include "ltrn1o.mm"
include "adantrr.mm"
include "f1of.mm"
include "fcoi1.mm"
include "3syl.mm"
include "tendo0pl.mm"
include "3eqtrrd.mm"

theorem dvhopN
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume dvhop.b: |- B = ( Base ` K )
  assume dvhop.h: |- H = ( LHyp ` K )
  assume dvhop.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhop.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhop.p: |- P = ( a e. E , b e. E |-> ( c e. T |-> ( ( a ` c ) o. ( b ` c ) ) ) )
  assume dvhop.a: |- A = ( f e. ( T X. E ) , g e. ( T X. E ) |-> <. ( ( 1st ` f ) o. ( 1st ` g ) ) , ( ( 2nd ` f ) P ( 2nd ` g ) ) >. )
  assume dvhop.s: |- S = ( s e. E , f e. ( T X. E ) |-> <. ( s ` ( 1st ` f ) ) , ( s o. ( 2nd ` f ) ) >. )
  assume dvhop.o: |- O = ( c e. T |-> ( _I |` B ) )

  disjoint B c
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a s
  disjoint E a
  disjoint b f
  disjoint b g
  disjoint b s
  disjoint E b
  disjoint f g
  disjoint f s
  disjoint E f
  disjoint g s
  disjoint E g
  disjoint E s
  disjoint H c
  disjoint K c
  disjoint P f
  disjoint P g
  disjoint a c
  disjoint T a
  disjoint b c
  disjoint T b
  disjoint c f
  disjoint c g
  disjoint c s
  disjoint T c
  disjoint T f
  disjoint T g
  disjoint T s
  disjoint W a
  disjoint W b
  disjoint W c
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ U e. E ) ) -> <. F , U >. = ( <. F , O >. A ( U S <. ( _I |` B ) , ( _I |` T ) >. ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    cU
    cE
    wcel
    #
    wa
    #
    wa
    #
    cF
    cO
    cop
    #
    cU
    cid
    cB
    cres
    #
    cid
    cT
    cres
    #
    cop
    cS
    co
    #
    cA
    co
    @5
    @6
    cU
    cop
    #
    cA
    co
    #
    cF
    @6
    ccom
    #
    cO
    cU
    cP
    co
    #
    cop
    #
    cF
    cU
    cop
    @4
    @8
    @9
    @5
    cA
    @4
    @8
    @6
    cU
    cfv
    #
    cU
    @7
    ccom
    #
    cop
    #
    @9
    @4
    @2
    @6
    cT
    wcel
    #
    @7
    cE
    wcel
    #
    @8
    @16
    wceq
    @0
    @1
    @2
    simprr
    #
    @0
    @17
    @3
    cB
    cT
    cH
    cK
    cW
    dvhop.b
    dvhop.h
    dvhop.t
    idltrn
    adantr
    #
    @0
    @18
    @3
    cT
    cE
    cH
    cK
    cW
    dvhop.h
    dvhop.t
    dvhop.e
    tendoidcl
    adantr
    cU
    cS
    cT
    @7
    vf
    cE
    @6
    vs
    dvhop.s
    dvhopspN
    syl12anc
    @4
    @14
    @6
    @15
    cU
    @0
    @2
    @14
    @6
    wceq
    @1
    cB
    cU
    cE
    cH
    cK
    cW
    dvhop.b
    dvhop.h
    dvhop.e
    tendoid
    adantrl
    @0
    @2
    @15
    cU
    wceq
    @1
    cT
    cU
    cE
    cH
    cK
    cW
    dvhop.h
    dvhop.t
    dvhop.e
    tendo1mulr
    adantrl
    opeq12d
    eqtrd
    oveq2d
    @4
    @1
    cO
    cE
    wcel
    #
    @17
    @2
    @10
    @13
    wceq
    @0
    @1
    @2
    simprl
    @0
    @21
    @3
    cB
    cT
    vc
    cE
    cH
    cK
    cO
    cW
    dvhop.b
    dvhop.h
    dvhop.t
    dvhop.e
    dvhop.o
    tendo0cl
    adantr
    @20
    @19
    cA
    cP
    cT
    cO
    vf
    vg
    cE
    cF
    @6
    cU
    dvhop.a
    dvhopaddN
    syl22anc
    @4
    @11
    cF
    @12
    cU
    @4
    cB
    cB
    cF
    wf1o
    #
    cB
    cB
    cF
    wf
    @11
    cF
    wceq
    @0
    @1
    @22
    @2
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    dvhop.b
    dvhop.h
    dvhop.t
    ltrn1o
    adantrr
    cB
    cB
    cF
    f1of
    cB
    cB
    cF
    fcoi1
    3syl
    @0
    @2
    @12
    cU
    wceq
    @1
    vb
    cB
    cP
    cU
    cT
    vc
    cE
    cH
    cK
    cO
    cW
    va
    dvhop.b
    dvhop.h
    dvhop.t
    dvhop.e
    dvhop.o
    dvhop.p
    tendo0pl
    adantrl
    opeq12d
    3eqtrrd
end
