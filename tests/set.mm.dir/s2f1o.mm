include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cs2.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "wf1o.mm"
include "wa.mm"
include "cop.mm"
include "cz.mm"
include "simpl1.mm"
include "0z.mm"
include "jctil.mm"
include "simpl2.mm"
include "1z.mm"
include "jca.mm"
include "simpl3.mm"
include "0ne1.mm"
include "f1oprg.mm"
include "sylc.mm"
include "eqcom.mm"
include "s2prop.mm"
include "3adant3.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "biimpa.mm"
include "eqidd.mm"
include "f1oeq123d.mm"
include "mpbid.mm"
include "ex.mm"

theorem s2f1o
  let cA: class A
  let cB: class B
  let cS: class S
  let cE: class E


  assert |- ( ( A e. S /\ B e. S /\ A =/= B ) -> ( E = <" A B "> -> E : { 0 , 1 } -1-1-onto-> { A , B } ) )

  proof
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cE
    cA
    cB
    cs2
    #
    wceq
    #
    cc0
    c1
    cpr
    #
    cA
    cB
    cpr
    #
    cE
    wf1o
    #
    @3
    @5
    wa
    #
    @6
    @7
    cc0
    cA
    cop
    c1
    cB
    cop
    cpr
    #
    wf1o
    #
    @8
    @9
    cc0
    cz
    wcel
    #
    @0
    wa
    #
    c1
    cz
    wcel
    #
    @1
    wa
    #
    wa
    cc0
    c1
    wne
    #
    @2
    wa
    @11
    @9
    @13
    @15
    @9
    @0
    @12
    @0
    @1
    @2
    @5
    simpl1
    0z
    jctil
    @9
    @1
    @14
    @0
    @1
    @2
    @5
    simpl2
    1z
    jctil
    jca
    @9
    @2
    @16
    @0
    @1
    @2
    @5
    simpl3
    0ne1
    jctil
    cc0
    cA
    c1
    cB
    cz
    cS
    cz
    cS
    f1oprg
    sylc
    @9
    @6
    @6
    @7
    @7
    @10
    cE
    @3
    @5
    @10
    cE
    wceq
    #
    @5
    @4
    cE
    wceq
    @3
    @17
    cE
    @4
    eqcom
    @3
    @4
    @10
    cE
    @0
    @1
    @4
    @10
    wceq
    @2
    cA
    cB
    cS
    s2prop
    3adant3
    eqeq1d
    syl5bb
    biimpa
    @9
    @6
    eqidd
    @9
    @7
    eqidd
    f1oeq123d
    mpbid
    ex
end
