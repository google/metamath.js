include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "cop.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "weq.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "dihordlem7.mm"
include "simpld.mm"
include "simprd.mm"
include "fveq1d.mm"
include "simp1.mm"
include "lhpocnel2.mm"
include "3ad2ant1.mm"
include "simp2r.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "tendo02.mm"
include "syl.mm"
include "eqtr3d.mm"
include "coeq1d.mm"
include "wf1o.mm"
include "wf.mm"
include "simp32.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "3eqtrd.mm"
include "jca.mm"

theorem dihordlem7b
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( s e. E /\ g e. T /\ <. f , O >. = ( <. ( s ` G ) , s >. .+ <. g , O >. ) ) ) -> ( f = g /\ O = s ) )

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
    vf
    cv
    #
    cO
    cop
    cG
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
    wceq
    #
    w3a
    #
    w3a
    #
    vf
    vg
    weq
    cO
    @4
    wceq
    #
    @12
    @8
    @9
    @6
    ccom
    #
    cid
    cB
    cres
    #
    @6
    ccom
    #
    @6
    @12
    @8
    @14
    wceq
    #
    @13
    cA
    cB
    cP
    c.pl
    cQ
    cR
    cT
    cU
    vf
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
    dihordlem7
    #
    simpld
    @12
    @9
    @15
    @6
    @12
    cG
    cO
    cfv
    #
    @9
    @15
    @12
    cG
    cO
    @4
    @12
    @17
    @13
    @18
    simprd
    #
    fveq1d
    @12
    cG
    cT
    wcel
    #
    @19
    @15
    wceq
    @12
    @0
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    @2
    @21
    @0
    @3
    @11
    simp1
    #
    @0
    @3
    @22
    @11
    cA
    cP
    cH
    cK
    c.le
    cW
    dihordlem8.l
    dihordlem8.a
    dihordlem8.h
    dihordlem8.p
    lhpocnel2
    3ad2ant1
    @0
    @1
    @2
    @11
    simp2r
    cA
    cP
    cR
    cT
    vh
    cG
    cH
    cK
    c.le
    cW
    dihordlem8.l
    dihordlem8.a
    dihordlem8.h
    dihordlem8.t
    dihordlem8.g
    ltrniotacl
    syl3anc
    cB
    cT
    vh
    cG
    cK
    cO
    dihordlem8.o
    dihordlem8.b
    tendo02
    syl
    eqtr3d
    coeq1d
    @12
    cB
    cB
    @6
    wf1o
    #
    cB
    cB
    @6
    wf
    @16
    @6
    wceq
    @12
    @0
    @7
    @24
    @23
    @0
    @3
    @5
    @7
    @10
    simp32
    cB
    cT
    @6
    cH
    cK
    chlt
    cW
    dihordlem8.b
    dihordlem8.h
    dihordlem8.t
    ltrn1o
    syl2anc
    cB
    cB
    @6
    f1of
    cB
    cB
    @6
    fcoi2
    3syl
    3eqtrd
    @20
    jca
end
