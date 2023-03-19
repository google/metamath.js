include "com.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "csuc.mm"
include "cdif.mm"
include "cint.mm"
include "con0.mm"
include "c0.mm"
include "wne.mm"
include "omsson.mm"
include "sstr.mm"
include "mpan2.mm"
include "ssdifssd.mm"
include "ad2antrr.mm"
include "ssel.mm"
include "peano2b.mm"
include "syl6ib.mm"
include "wceq.mm"
include "eleq1.mm"
include "rexbidv.mm"
include "rspccva.mm"
include "wn.mm"
include "wi.mm"
include "word.mm"
include "nnord.mm"
include "ordn2lp.mm"
include "imnan.mm"
include "sylibr.mm"
include "con2d.mm"
include "syl.mm"
include "syl6.mm"
include "imdistand.mm"
include "eldif.mm"
include "ne0i.mm"
include "sylbir.mm"
include "expd.mm"
include "rexlimdv.mm"
include "syl5.mm"
include "sylan2d.mm"
include "impl.mm"
include "onint.mm"
include "syl2anc.mm"
include "eldifad.mm"

theorem unblem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( ( ( B C_ _om /\ A. x e. _om E. y e. B x e. y ) /\ A e. B ) -> |^| ( B \ suc A ) e. B )

  proof
    cB
    com
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    vy
    cB
    wrex
    #
    vx
    com
    wral
    #
    wa
    cA
    cB
    wcel
    #
    wa
    #
    cB
    cA
    csuc
    #
    cdif
    #
    cint
    #
    cB
    @8
    @7
    @9
    con0
    wss
    #
    @9
    c0
    wne
    #
    @10
    @9
    wcel
    @0
    @11
    @5
    @6
    @0
    cB
    con0
    @8
    @0
    com
    con0
    wss
    cB
    con0
    wss
    omsson
    cB
    com
    con0
    sstr
    mpan2
    ssdifssd
    ad2antrr
    @0
    @5
    @6
    @12
    @0
    @6
    @8
    com
    wcel
    #
    @5
    @12
    @0
    @6
    cA
    com
    wcel
    @13
    cB
    com
    cA
    ssel
    cA
    peano2b
    syl6ib
    @5
    @13
    wa
    @8
    @2
    wcel
    #
    vy
    cB
    wrex
    #
    @0
    @12
    @4
    @15
    vx
    @8
    com
    @1
    @8
    wceq
    @3
    @14
    vy
    cB
    @1
    @8
    @2
    eleq1
    rexbidv
    rspccva
    @0
    @14
    @12
    vy
    cB
    @0
    @2
    cB
    wcel
    #
    @14
    @12
    @0
    @16
    @14
    wa
    @16
    @2
    @8
    wcel
    #
    wn
    #
    wa
    #
    @12
    @0
    @16
    @14
    @18
    @0
    @16
    @2
    com
    wcel
    #
    @14
    @18
    wi
    #
    cB
    com
    @2
    ssel
    @20
    @2
    word
    #
    @21
    @2
    nnord
    @22
    @17
    @14
    @22
    @17
    @14
    wa
    wn
    @17
    @14
    wn
    wi
    @2
    @8
    ordn2lp
    @17
    @14
    imnan
    sylibr
    con2d
    syl
    syl6
    imdistand
    @19
    @2
    @9
    wcel
    @12
    @2
    cB
    @8
    eldif
    @9
    @2
    ne0i
    sylbir
    syl6
    expd
    rexlimdv
    syl5
    sylan2d
    impl
    @9
    onint
    syl2anc
    eldifad
end
