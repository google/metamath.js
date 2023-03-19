include "wcel.mm"
include "w3a.mm"
include "wf1o.mm"
include "cfv.mm"
include "wceq.mm"
include "symgextf1o.mm"
include "3adant1.mm"
include "simp2.mm"
include "cv.mm"
include "cif.mm"
include "iftrue.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "cmpt.mm"
include "mptexg.mm"
include "3ad2ant1.mm"
include "syl5eqel.mm"
include "symgfixelq.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem symgfixfolem1
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cE: class E
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cZ: class Z
  let vq: setvar q
  let vg: setvar g
  let vp: setvar p
  let vi: setvar i
  assume symgfixf.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume symgfixf.q: |- Q = { q e. P | ( q ` K ) = K }
  assume symgfixf.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgfixf.h: |- H = ( q e. Q |-> ( q |` ( N \ { K } ) ) )
  assume symgfixfo.e: |- E = ( x e. N |-> if ( x = K , K , ( Z ` x ) ) )

  disjoint E x
  disjoint K x
  disjoint N x
  disjoint S x
  disjoint V x
  disjoint Z x
  disjoint K q
  disjoint P q
  disjoint N q
  disjoint Q q
  disjoint S q
  disjoint H g
  disjoint H p
  disjoint g p
  disjoint K g
  disjoint K i
  disjoint K p
  disjoint g i
  disjoint i p
  disjoint N g
  disjoint N i
  disjoint N p
  disjoint g q
  disjoint i q
  disjoint p q
  disjoint Q g
  disjoint Q p
  assert |- ( ( N e. V /\ K e. N /\ Z e. S ) -> E e. Q )

  proof
    cN
    cV
    wcel
    #
    cK
    cN
    wcel
    #
    cZ
    cS
    wcel
    #
    w3a
    #
    cE
    cQ
    wcel
    #
    cN
    cN
    cE
    wf1o
    #
    cK
    cE
    cfv
    cK
    wceq
    #
    @1
    @2
    @5
    @0
    vx
    cS
    cE
    cK
    cN
    cZ
    symgfixf.s
    symgfixfo.e
    symgextf1o
    3adant1
    @3
    @1
    @1
    @6
    @0
    @1
    @2
    simp2
    #
    @7
    vx
    cK
    vx
    cv
    #
    cK
    wceq
    #
    cK
    @8
    cZ
    cfv
    #
    cif
    #
    cK
    cN
    cN
    cE
    @9
    cK
    @10
    iftrue
    symgfixfo.e
    fvmptg
    syl2anc
    @3
    cE
    cvv
    wcel
    @4
    @5
    @6
    wa
    wb
    @3
    cE
    vx
    cN
    @11
    cmpt
    #
    cvv
    symgfixfo.e
    @0
    @1
    @12
    cvv
    wcel
    @2
    vx
    cN
    @11
    cV
    mptexg
    3ad2ant1
    syl5eqel
    cP
    cQ
    cE
    cK
    cN
    cvv
    vq
    symgfixf.p
    symgfixf.q
    symgfixelq
    syl
    mpbir2and
end
