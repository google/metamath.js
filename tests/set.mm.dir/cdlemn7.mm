include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "ccom.mm"
include "simp33.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp31.mm"
include "simp32.mm"
include "cdlemn6.mm"
include "syl122anc.mm"
include "eqtrd.mm"
include "fvex.mm"
include "vex.mm"
include "coex.mm"
include "opth2.mm"
include "sylib.mm"

theorem cdlemn7
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  assume cdlemn8.b: |- B = ( Base ` K )
  assume cdlemn8.l: |- .<_ = ( le ` K )
  assume cdlemn8.a: |- A = ( Atoms ` K )
  assume cdlemn8.h: |- H = ( LHyp ` K )
  assume cdlemn8.p: |- P = ( ( oc ` K ) ` W )
  assume cdlemn8.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume cdlemn8.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemn8.e: |- E = ( ( TEndo ` K ) ` W )
  assume cdlemn8.u: |- U = ( ( DVecH ` K ) ` W )
  assume cdlemn8.s: |- .+ = ( +g ` U )
  assume cdlemn8.f: |- F = ( iota_ h e. T ( h ` P ) = Q )
  assume cdlemn8.g: |- G = ( iota_ h e. T ( h ` P ) = R )

  disjoint .<_ h
  disjoint A h
  disjoint B h
  disjoint H h
  disjoint K h
  disjoint T h
  disjoint P h
  disjoint Q h
  disjoint W h
  disjoint h t
  disjoint h u
  disjoint t u
  disjoint K t
  disjoint K u
  disjoint T t
  disjoint T u
  disjoint E t
  disjoint E u
  disjoint W t
  disjoint W u
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( s e. E /\ g e. T /\ <. G , ( _I |` T ) >. = ( <. ( s ` F ) , s >. .+ <. g , O >. ) ) ) -> ( G = ( ( s ` F ) o. g ) /\ ( _I |` T ) = s ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    wa
    #
    vs
    cv
    #
    cE
    wcel
    #
    vg
    cv
    #
    cT
    wcel
    #
    cG
    cid
    cT
    cres
    #
    cop
    #
    cF
    @4
    cfv
    #
    @4
    cop
    @6
    cO
    cop
    c.pl
    co
    #
    wceq
    #
    w3a
    #
    w3a
    #
    @9
    @10
    @6
    ccom
    #
    @4
    cop
    #
    wceq
    cG
    @15
    wceq
    @8
    @4
    wceq
    wa
    @14
    @9
    @11
    @16
    @0
    @3
    @5
    @7
    @12
    simp33
    @14
    @0
    @1
    @2
    @5
    @7
    @11
    @16
    wceq
    @0
    @3
    @13
    simp1
    @0
    @1
    @2
    @13
    simp2l
    @0
    @1
    @2
    @13
    simp2r
    @0
    @3
    @5
    @7
    @12
    simp31
    @0
    @3
    @5
    @7
    @12
    simp32
    cA
    cB
    cP
    c.pl
    cQ
    cR
    cT
    cU
    vg
    vh
    cE
    cF
    cH
    cK
    c.le
    cO
    cW
    vs
    cdlemn8.b
    cdlemn8.l
    cdlemn8.a
    cdlemn8.h
    cdlemn8.p
    cdlemn8.o
    cdlemn8.t
    cdlemn8.e
    cdlemn8.u
    cdlemn8.s
    cdlemn8.f
    cdlemn6
    syl122anc
    eqtrd
    cG
    @8
    @15
    @4
    @10
    @6
    cF
    @4
    fvex
    vg
    vex
    coex
    vs
    vex
    opth2
    sylib
end
