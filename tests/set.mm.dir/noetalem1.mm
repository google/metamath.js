include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "cbday.mm"
include "cima.mm"
include "cuni.mm"
include "csuc.mm"
include "cdm.mm"
include "cdif.mm"
include "c1o.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "con0.mm"
include "nosupno.mm"
include "3adant3.mm"
include "bdayimaon.mm"
include "3ad2ant3.mm"
include "c2o.mm"
include "1on.mm"
include "elexi.mm"
include "prid1.mm"
include "noextendseq.mm"
include "syl2anc.mm"
include "syl5eqel.mm"

theorem noetalem1
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  let vg: setvar g
  let cZ: class Z
  assume noetalem.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )
  assume noetalem.2: |- Z = ( S u. ( ( suc U. ( bday " B ) \ dom S ) X. { 1o } ) )

  disjoint A g
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  assert |- ( ( A C_ No /\ A e. _V /\ B e. _V ) -> Z e. No )

  proof
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    w3a
    #
    cZ
    cS
    cbday
    cB
    cima
    cuni
    csuc
    #
    cS
    cdm
    cdif
    c1o
    csn
    cxp
    cun
    #
    csur
    noetalem.2
    @3
    cS
    csur
    wcel
    #
    @4
    con0
    wcel
    #
    @5
    csur
    wcel
    @0
    @1
    @6
    @2
    vx
    vy
    vv
    vu
    cA
    cS
    vg
    cvv
    noetalem.1
    nosupno
    3adant3
    @2
    @0
    @7
    @1
    cB
    cvv
    bdayimaon
    3ad2ant3
    cS
    @4
    c1o
    c1o
    c2o
    c1o
    con0
    1on
    elexi
    prid1
    noextendseq
    syl2anc
    syl5eqel
end
