include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wi.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cv.mm"
include "cwlks.mm"
include "simp1.mm"
include "simp2.mm"
include "syl6eleq.mm"
include "simp3.mm"
include "copab.mm"
include "wksv.mm"
include "a1i.mm"
include "mptmpt2opabovd.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "breqd.mm"
include "anbi12d.mm"
include "bropfvvvv.mm"
include "mp2an.mm"
include "3anass.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "sylibr.mm"
include "biimpd.mm"
include "imdistani.mm"
include "mpancom.mm"

theorem wksonproplem
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cO: class O
  let cV: class V
  let cW: class W
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assume wksonproplem.v: |- V = ( Vtx ` G )
  assume wksonproplem.b: |- ( ( ( G e. _V /\ A e. V /\ B e. V ) /\ ( F e. _V /\ P e. _V ) ) -> ( F ( A ( W ` G ) B ) P <-> ( F ( A ( O ` G ) B ) P /\ F ( Q ` G ) P ) ) )
  assume wksonproplem.d: |- W = ( g e. _V |-> ( a e. ( Vtx ` g ) , b e. ( Vtx ` g ) |-> { <. f , p >. | ( f ( a ( O ` g ) b ) p /\ f ( Q ` g ) p ) } ) )
  assume wksonproplem.w: |- ( ( ( G e. _V /\ A e. V /\ B e. V ) /\ f ( Q ` G ) p ) -> f ( Walks ` G ) p )

  disjoint A a
  disjoint A b
  disjoint A f
  disjoint A g
  disjoint A p
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a p
  disjoint b f
  disjoint b g
  disjoint b p
  disjoint f g
  disjoint f p
  disjoint g p
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B g
  disjoint B p
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G g
  disjoint G p
  disjoint O a
  disjoint O b
  disjoint O g
  disjoint Q a
  disjoint Q b
  disjoint Q g
  disjoint V a
  disjoint V b
  disjoint V f
  disjoint V g
  disjoint V p
  assert |- ( F ( A ( W ` G ) B ) P -> ( ( G e. _V /\ A e. V /\ B e. V ) /\ ( F e. _V /\ P e. _V ) /\ ( F ( A ( O ` G ) B ) P /\ F ( Q ` G ) P ) ) )

  proof
    cF
    cP
    cA
    cB
    cG
    cW
    cfv
    co
    wbr
    #
    cG
    cvv
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    wa
    #
    wa
    #
    cF
    cP
    cA
    cB
    cG
    cO
    cfv
    #
    co
    #
    wbr
    cF
    cP
    cG
    cQ
    cfv
    #
    wbr
    wa
    #
    wa
    #
    @4
    @5
    @10
    w3a
    @6
    @0
    @11
    @0
    @1
    @2
    @3
    wa
    #
    @5
    w3a
    #
    @6
    cV
    cvv
    wcel
    #
    @14
    @0
    @13
    wi
    cV
    cG
    cvtx
    cfv
    #
    cvv
    wksonproplem.v
    cG
    cvtx
    fvex
    eqeltri
    #
    @16
    vf
    cv
    #
    vp
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    vg
    cv
    #
    cO
    cfv
    #
    co
    #
    wbr
    #
    @17
    @18
    @21
    cQ
    cfv
    #
    wbr
    #
    wa
    @17
    @18
    @19
    @20
    @7
    co
    #
    wbr
    #
    @17
    @18
    @9
    wbr
    #
    wa
    @17
    @18
    @8
    wbr
    @29
    wa
    cG
    cA
    cB
    cF
    cV
    cV
    cvv
    vp
    cP
    cW
    @21
    cvtx
    cfv
    #
    @30
    cvv
    cvv
    vg
    va
    vb
    vf
    wksonproplem.d
    @4
    @17
    @18
    cG
    cwlks
    cfv
    wbr
    #
    cvtx
    cvtx
    cO
    cQ
    vf
    vg
    vp
    cG
    cW
    cvv
    cvv
    cA
    cB
    va
    vb
    @1
    @2
    @3
    simp1
    @4
    cA
    cV
    @15
    @1
    @2
    @3
    simp2
    wksonproplem.v
    syl6eleq
    @4
    cB
    cV
    @15
    @1
    @2
    @3
    simp3
    wksonproplem.v
    syl6eleq
    @31
    vf
    vp
    copab
    cvv
    wcel
    @4
    vf
    cG
    vp
    wksv
    a1i
    wksonproplem.w
    wksonproplem.d
    mptmpt2opabovd
    @21
    cG
    wceq
    #
    @30
    @15
    cV
    @21
    cG
    cvtx
    fveq2
    wksonproplem.v
    syl6eqr
    #
    @33
    @32
    @24
    @28
    @26
    @29
    @32
    @23
    @27
    @17
    @18
    @32
    @22
    @7
    @19
    @20
    @21
    cG
    cO
    fveq2
    oveqd
    breqd
    @32
    @25
    @9
    @17
    @18
    @21
    cG
    cQ
    fveq2
    breqd
    anbi12d
    bropfvvvv
    mp2an
    @6
    @1
    @12
    wa
    #
    @5
    wa
    @13
    @4
    @34
    @5
    @1
    @2
    @3
    3anass
    anbi1i
    @1
    @12
    @5
    df-3an
    bitr4i
    sylibr
    @6
    @0
    @10
    @6
    @0
    @10
    wksonproplem.b
    biimpd
    imdistani
    mpancom
    @4
    @5
    @10
    df-3an
    sylibr
end
