include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "w3a.mm"
include "cfv.mm"
include "cop.mm"
include "co.mm"
include "ccom.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp2l.mm"
include "simp3.mm"
include "cdlemn6.mm"
include "syl121anc.mm"

theorem dihordlem6
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
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cW: class W
  let vs: setvar s
  assume dihordlem8.b: |- B = ( Base ` K )
  assume dihordlem8.l: |- .<_ = ( le ` K )
  assume dihordlem8.a: |- A = ( Atoms ` K )
  assume dihordlem8.h: |- H = ( LHyp ` K )
  assume dihordlem8.p: |- P = ( ( oc ` K ) ` W )
  assume dihordlem8.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume dihordlem8.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihordlem8.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihordlem8.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihordlem8.s: |- .+ = ( +g ` U )
  assume dihordlem8.g: |- G = ( iota_ h e. T ( h ` P ) = R )

  disjoint .<_ h
  disjoint A h
  disjoint B h
  disjoint H h
  disjoint K h
  disjoint P h
  disjoint R h
  disjoint T h
  disjoint W h
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( s e. E /\ g e. T ) ) -> ( <. ( s ` G ) , s >. .+ <. g , O >. ) = <. ( ( s ` G ) o. g ) , s >. )

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
    vg
    cv
    #
    cT
    wcel
    wa
    #
    w3a
    @0
    @2
    @1
    @6
    cG
    @4
    cfv
    #
    @4
    cop
    @5
    cO
    cop
    c.pl
    co
    @7
    @5
    ccom
    @4
    cop
    wceq
    @0
    @3
    @6
    simp1
    @0
    @1
    @2
    @6
    simp2r
    @0
    @1
    @2
    @6
    simp2l
    @0
    @3
    @6
    simp3
    cA
    cB
    cP
    c.pl
    cR
    cQ
    cT
    cU
    vg
    vh
    cE
    cG
    cH
    cK
    c.le
    cO
    cW
    vs
    dihordlem8.b
    dihordlem8.l
    dihordlem8.a
    dihordlem8.h
    dihordlem8.p
    dihordlem8.o
    dihordlem8.t
    dihordlem8.e
    dihordlem8.u
    dihordlem8.s
    dihordlem8.g
    cdlemn6
    syl121anc
end
