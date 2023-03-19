include "wrel.mm"
include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "c0.mm"
include "snprc.mm"
include "imaeq2.mm"
include "sylbi.mm"
include "ima0.mm"
include "syl6eq.mm"
include "adantl.mm"
include "wex.mm"
include "brrelex.mm"
include "stoic1a.mm"
include "nexdv.mm"
include "abn0.mm"
include "necon1bbii.mm"
include "sylib.mm"
include "eqtr4d.mm"
include "ex.mm"
include "imasng.mm"
include "pm2.61d2.mm"

theorem relimasn
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vx: setvar x
  let cB: class B

  disjoint A y
  disjoint R y
  disjoint x y
  disjoint A x
  disjoint B x
  disjoint R x
  assert |- ( Rel R -> ( R " { A } ) = { y | A R y } )

  proof
    cR
    wrel
    #
    cA
    cvv
    wcel
    #
    cR
    cA
    csn
    #
    cima
    #
    cA
    vy
    cv
    #
    cR
    wbr
    #
    vy
    cab
    #
    wceq
    #
    @0
    @1
    wn
    #
    @7
    @0
    @8
    wa
    #
    @3
    c0
    @6
    @8
    @3
    c0
    wceq
    @0
    @8
    @3
    cR
    c0
    cima
    #
    c0
    @8
    @2
    c0
    wceq
    @3
    @10
    wceq
    cA
    snprc
    @2
    c0
    cR
    imaeq2
    sylbi
    cR
    ima0
    syl6eq
    adantl
    @9
    @5
    vy
    wex
    #
    wn
    @6
    c0
    wceq
    @9
    @5
    vy
    @0
    @5
    @1
    cA
    @4
    cR
    brrelex
    stoic1a
    nexdv
    @11
    @6
    c0
    @5
    vy
    abn0
    necon1bbii
    sylib
    eqtr4d
    ex
    vy
    cA
    cvv
    cR
    imasng
    pm2.61d2
end
