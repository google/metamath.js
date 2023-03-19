include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "wss.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "iccssre.mm"
include "sstr.mm"
include "ancoms.mm"
include "sylan.mm"
include "3adant3.mm"
include "ne0i.mm"
include "3ad2ant3.mm"
include "simplr.mm"
include "ssel.mm"
include "elicc2.mm"
include "biimpd.mm"
include "sylan9r.mm"
include "imp.mm"
include "simp3d.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "3jca.mm"

theorem iccsupr
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S

  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x y
  disjoint S x
  disjoint S y
  assert |- ( ( ( A e. RR /\ B e. RR ) /\ S C_ ( A [,] B ) /\ C e. S ) -> ( S C_ RR /\ S =/= (/) /\ E. x e. RR A. y e. S y <_ x ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cS
    cA
    cB
    cicc
    co
    #
    wss
    #
    cC
    cS
    wcel
    #
    w3a
    cS
    cr
    wss
    #
    cS
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cS
    wral
    #
    vx
    cr
    wrex
    #
    @2
    @4
    @6
    @5
    @2
    @3
    cr
    wss
    #
    @4
    @6
    cA
    cB
    iccssre
    @4
    @13
    @6
    cS
    @3
    cr
    sstr
    ancoms
    sylan
    3adant3
    @5
    @2
    @7
    @4
    cS
    cC
    ne0i
    3ad2ant3
    @2
    @4
    @12
    @5
    @2
    @4
    wa
    #
    @1
    @8
    cB
    cle
    wbr
    #
    vy
    cS
    wral
    #
    @12
    @0
    @1
    @4
    simplr
    @14
    @15
    vy
    cS
    @14
    @8
    cS
    wcel
    #
    wa
    @8
    cr
    wcel
    #
    cA
    @8
    cle
    wbr
    #
    @15
    @14
    @17
    @18
    @19
    @15
    w3a
    #
    @4
    @17
    @8
    @3
    wcel
    #
    @2
    @20
    cS
    @3
    @8
    ssel
    @2
    @21
    @20
    cA
    cB
    @8
    elicc2
    biimpd
    sylan9r
    imp
    simp3d
    ralrimiva
    @11
    @16
    vx
    cB
    cr
    @9
    cB
    wceq
    @10
    @15
    vy
    cS
    @9
    cB
    @8
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    3adant3
    3jca
end
