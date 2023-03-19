include "wwe.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "ccnv.mm"
include "wor.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wess.mm"
include "impcom.mm"
include "weso.mm"
include "syl.mm"
include "cnvso.mm"
include "sylib.mm"
include "3ad2antr2.mm"
include "wfr.mm"
include "wefr.mm"
include "ssid.mm"
include "a1i.mm"
include "3anim2i.mm"
include "adantl.mm"
include "frinfm.mm"
include "syl2anc.mm"
include "jca.mm"

theorem welb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( ( R We A /\ ( B e. C /\ B C_ A /\ B =/= (/) ) ) -> ( `' R Or B /\ E. x e. B ( A. y e. B -. x `' R y /\ A. y e. B ( y `' R x -> E. z e. B y `' R z ) ) ) )

  proof
    cA
    cR
    wwe
    #
    cB
    cC
    wcel
    #
    cB
    cA
    wss
    #
    cB
    c0
    wne
    #
    w3a
    #
    wa
    #
    cB
    cR
    ccnv
    #
    wor
    #
    vx
    cv
    #
    vy
    cv
    #
    @6
    wbr
    wn
    vy
    cB
    wral
    @9
    @8
    @6
    wbr
    @9
    vz
    cv
    @6
    wbr
    vz
    cB
    wrex
    wi
    vy
    cB
    wral
    wa
    vx
    cB
    wrex
    #
    @0
    @1
    @2
    @7
    @3
    @0
    @2
    wa
    #
    cB
    cR
    wor
    #
    @7
    @11
    cB
    cR
    wwe
    #
    @12
    @2
    @0
    @13
    cB
    cA
    cR
    wess
    impcom
    #
    cB
    cR
    weso
    syl
    cB
    cR
    cnvso
    sylib
    3ad2antr2
    @5
    cB
    cR
    wfr
    #
    @1
    cB
    cB
    wss
    #
    @3
    w3a
    #
    @10
    @0
    @1
    @2
    @15
    @3
    @11
    @13
    @15
    @14
    cB
    cR
    wefr
    syl
    3ad2antr2
    @4
    @17
    @0
    @2
    @16
    @1
    @3
    @16
    @2
    cB
    ssid
    a1i
    3anim2i
    adantl
    vx
    vy
    vz
    cB
    cB
    cC
    cR
    frinfm
    syl2anc
    jca
end
