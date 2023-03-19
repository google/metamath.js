include "cab.mm"
include "cint.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "ssintab.mm"
include "simpr.mm"
include "ancr.mm"
include "impbid2.mm"
include "imbi1d.mm"
include "alimi.mm"
include "albi.mm"
include "syl.mm"
include "sylbi.mm"
include "vex.mm"
include "elintab.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem intmin4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( A C_ |^| { x | ph } -> |^| { x | ( A C_ x /\ ph ) } = |^| { x | ph } )

  proof
    cA
    wph
    vx
    cab
    cint
    #
    wss
    #
    vy
    cA
    vx
    cv
    #
    wss
    #
    wph
    wa
    #
    vx
    cab
    cint
    #
    @0
    @1
    @4
    vy
    cv
    #
    @2
    wcel
    #
    wi
    #
    vx
    wal
    #
    wph
    @7
    wi
    #
    vx
    wal
    #
    @6
    @5
    wcel
    @6
    @0
    wcel
    @1
    wph
    @3
    wi
    #
    vx
    wal
    #
    @9
    @11
    wb
    #
    wph
    vx
    cA
    ssintab
    @13
    @8
    @10
    wb
    #
    vx
    wal
    @14
    @12
    @15
    vx
    @12
    @4
    wph
    @7
    @12
    @4
    wph
    @3
    wph
    simpr
    wph
    @3
    ancr
    impbid2
    imbi1d
    alimi
    @8
    @10
    vx
    albi
    syl
    sylbi
    @4
    vx
    @6
    vy
    vex
    #
    elintab
    wph
    vx
    @6
    @16
    elintab
    3bitr4g
    eqrdv
end
