include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "crdg.mm"
include "cfv.mm"
include "cima.mm"
include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "rdglim.mm"
include "cop.mm"
include "wex.mm"
include "dfima3.mm"
include "df-rex.mm"
include "con0.mm"
include "wb.mm"
include "word.mm"
include "wi.mm"
include "limord.mm"
include "ordelord.mm"
include "ex.mm"
include "vex.mm"
include "elon.mm"
include "syl6ibr.mm"
include "syl.mm"
include "eqcom.mm"
include "wfn.mm"
include "rdgfnon.mm"
include "fnopfvb.mm"
include "mpan.mm"
include "syl5bb.mm"
include "syl6.mm"
include "pm5.32d.mm"
include "exbidv.mm"
include "syl5rbb.mm"
include "abbidv.mm"
include "syl5eq.mm"
include "unieqd.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem rdglim2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  assert |- ( ( B e. C /\ Lim B ) -> ( rec ( F , A ) ` B ) = U. { y | E. x e. B y = ( rec ( F , A ) ` x ) } )

  proof
    cB
    cC
    wcel
    #
    cB
    wlim
    #
    wa
    cB
    cF
    cA
    crdg
    #
    cfv
    @2
    cB
    cima
    #
    cuni
    #
    vy
    cv
    #
    vx
    cv
    #
    @2
    cfv
    #
    wceq
    #
    vx
    cB
    wrex
    #
    vy
    cab
    #
    cuni
    #
    cA
    cB
    cC
    cF
    rdglim
    @1
    @4
    @11
    wceq
    @0
    @1
    @3
    @10
    @1
    @3
    @6
    cB
    wcel
    #
    @6
    @5
    cop
    @2
    wcel
    #
    wa
    #
    vx
    wex
    #
    vy
    cab
    @10
    vx
    vy
    @2
    cB
    dfima3
    @1
    @15
    @9
    vy
    @9
    @12
    @8
    wa
    #
    vx
    wex
    @1
    @15
    @8
    vx
    cB
    df-rex
    @1
    @16
    @14
    vx
    @1
    @12
    @8
    @13
    @1
    @12
    @6
    con0
    wcel
    #
    @8
    @13
    wb
    @1
    cB
    word
    #
    @12
    @17
    wi
    cB
    limord
    @18
    @12
    @6
    word
    #
    @17
    @18
    @12
    @19
    cB
    @6
    ordelord
    ex
    @6
    vx
    vex
    elon
    syl6ibr
    syl
    @8
    @7
    @5
    wceq
    #
    @17
    @13
    @5
    @7
    eqcom
    @2
    con0
    wfn
    @17
    @20
    @13
    wb
    cA
    cF
    rdgfnon
    con0
    @6
    @5
    @2
    fnopfvb
    mpan
    syl5bb
    syl6
    pm5.32d
    exbidv
    syl5rbb
    abbidv
    syl5eq
    unieqd
    adantl
    eqtrd
end
