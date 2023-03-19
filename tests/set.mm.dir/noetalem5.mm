include "csur.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wral.mm"
include "cbday.mm"
include "cfv.mm"
include "cun.mm"
include "cima.mm"
include "cuni.mm"
include "csuc.mm"
include "w3a.mm"
include "wrex.mm"
include "elex.mm"
include "anim2i.mm"
include "id.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2r.mm"
include "noetalem1.mm"
include "syl3anc.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplrr.mm"
include "simpr.mm"
include "noetalem2.mm"
include "syl31anc.mm"
include "ralrimiva.mm"
include "3adant3.mm"
include "noetalem3.mm"
include "noetalem4.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "breq1.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "syl3an.mm"

theorem noetalem5
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  let vg: setvar g
  let cV: class V
  let cW: class W
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  assume noetalem.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )
  assume noetalem.2: |- Z = ( S u. ( ( suc U. ( bday " B ) \ dom S ) X. { 1o } ) )

  disjoint A a
  disjoint a b
  disjoint A b
  disjoint a g
  disjoint A g
  disjoint a u
  disjoint A u
  disjoint a v
  disjoint A v
  disjoint a x
  disjoint A x
  disjoint a y
  disjoint A y
  disjoint a z
  disjoint A z
  disjoint B a
  disjoint B b
  disjoint b g
  disjoint b x
  disjoint b z
  disjoint B z
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint S a
  disjoint S g
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint Z a
  disjoint Z b
  disjoint Z z
  assert |- ( ( ( A C_ No /\ A e. V ) /\ ( B C_ No /\ B e. W ) /\ A. a e. A A. b e. B a <s b ) -> E. z e. No ( A. a e. A a <s z /\ A. b e. B z <s b /\ ( bday ` z ) C_ suc U. ( bday " ( A u. B ) ) ) )

  proof
    cA
    csur
    wss
    #
    cA
    cV
    wcel
    #
    wa
    @0
    cA
    cvv
    wcel
    #
    wa
    #
    cB
    csur
    wss
    #
    cB
    cW
    wcel
    #
    wa
    @4
    cB
    cvv
    wcel
    #
    wa
    #
    va
    cv
    #
    vb
    cv
    #
    cslt
    wbr
    vb
    cB
    wral
    va
    cA
    wral
    #
    @10
    @8
    vz
    cv
    #
    cslt
    wbr
    #
    va
    cA
    wral
    #
    @11
    @9
    cslt
    wbr
    #
    vb
    cB
    wral
    #
    @11
    cbday
    cfv
    #
    cbday
    cA
    cB
    cun
    cima
    cuni
    csuc
    #
    wss
    #
    w3a
    #
    vz
    csur
    wrex
    #
    @1
    @2
    @0
    cA
    cV
    elex
    anim2i
    @5
    @6
    @4
    cB
    cW
    elex
    anim2i
    @10
    id
    @3
    @7
    @10
    w3a
    #
    cZ
    csur
    wcel
    #
    @8
    cZ
    cslt
    wbr
    #
    va
    cA
    wral
    #
    cZ
    @9
    cslt
    wbr
    #
    vb
    cB
    wral
    #
    cZ
    cbday
    cfv
    #
    @17
    wss
    #
    @20
    @21
    @0
    @2
    @6
    @22
    @0
    @2
    @7
    @10
    simp1l
    @0
    @2
    @7
    @10
    simp1r
    @3
    @4
    @6
    @10
    simp2r
    vx
    vy
    vv
    vu
    cA
    cB
    cS
    vg
    cZ
    noetalem.1
    noetalem.2
    noetalem1
    syl3anc
    @3
    @7
    @24
    @10
    @3
    @7
    wa
    #
    @23
    va
    cA
    @29
    @8
    cA
    wcel
    #
    wa
    @0
    @2
    @6
    @30
    @23
    @0
    @2
    @7
    @30
    simplll
    @0
    @2
    @7
    @30
    simpllr
    @3
    @4
    @6
    @30
    simplrr
    @29
    @30
    simpr
    vx
    vy
    vv
    vu
    cA
    cB
    cS
    vg
    @8
    cZ
    noetalem.1
    noetalem.2
    noetalem2
    syl31anc
    ralrimiva
    3adant3
    vx
    vy
    vv
    vu
    cA
    cB
    cS
    vg
    cZ
    va
    vb
    noetalem.1
    noetalem.2
    noetalem3
    @3
    @7
    @28
    @10
    vx
    vy
    vv
    vu
    cA
    cB
    cS
    vg
    cZ
    noetalem.1
    noetalem.2
    noetalem4
    3adant3
    @19
    @24
    @26
    @28
    w3a
    vz
    cZ
    csur
    @11
    cZ
    wceq
    #
    @13
    @24
    @15
    @26
    @18
    @28
    @31
    @12
    @23
    va
    cA
    @11
    cZ
    @8
    cslt
    breq2
    ralbidv
    @31
    @14
    @25
    vb
    cB
    @11
    cZ
    @9
    cslt
    breq1
    ralbidv
    @31
    @16
    @27
    @17
    @11
    cZ
    cbday
    fveq2
    sseq1d
    3anbi123d
    rspcev
    syl13anc
    syl3an
end
