include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cuni.mm"
include "csn.mm"
include "wceq.mm"
include "cv.mm"
include "wex.mm"
include "en1.mm"
include "id.mm"
include "unieq.mm"
include "vex.mm"
include "unisn.mm"
include "syl6eq.mm"
include "sneqd.mm"
include "eqtr4d.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "cvv.mm"
include "wcel.mm"
include "snex.mm"
include "syl6eqel.mm"
include "uniexg.mm"
include "syl.mm"
include "ensn1g.mm"
include "eqbrtrd.mm"
include "impbii.mm"

theorem en1b
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let wph: wff ph


  assert |- ( A ~~ 1o <-> A = { U. A } )

  proof
    cA
    c1o
    cen
    wbr
    #
    cA
    cA
    cuni
    #
    csn
    #
    wceq
    #
    @0
    cA
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    wex
    @3
    vx
    cA
    en1
    @6
    @3
    vx
    @6
    cA
    @5
    @2
    @6
    id
    @6
    @1
    @4
    @6
    @1
    @5
    cuni
    @4
    cA
    @5
    unieq
    @4
    vx
    vex
    unisn
    syl6eq
    sneqd
    eqtr4d
    exlimiv
    sylbi
    @3
    cA
    @2
    c1o
    cen
    @3
    id
    #
    @3
    @1
    cvv
    wcel
    #
    @2
    c1o
    cen
    wbr
    @3
    cA
    cvv
    wcel
    @8
    @3
    cA
    @2
    cvv
    @7
    @1
    snex
    syl6eqel
    cA
    cvv
    uniexg
    syl
    @1
    cvv
    ensn1g
    syl
    eqbrtrd
    impbii
end
