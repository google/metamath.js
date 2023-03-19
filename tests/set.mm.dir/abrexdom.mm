include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "cv.mm"
include "wa.mm"
include "copab.mm"
include "crn.mm"
include "cdom.mm"
include "wex.mm"
include "df-rex.mm"
include "abbii.mm"
include "rnopab.mm"
include "eqtr4i.mm"
include "cdm.mm"
include "wbr.mm"
include "cvv.mm"
include "wfn.mm"
include "wss.mm"
include "dmopabss.mm"
include "ssexg.mm"
include "mpan.mm"
include "wfun.mm"
include "wmo.mm"
include "funopab.mm"
include "wi.mm"
include "moanimv.mm"
include "mpbir.mm"
include "mpgbir.mm"
include "a1i.mm"
include "funfn.mm"
include "sylib.mm"
include "fnrndomg.mm"
include "sylc.mm"
include "ssdomg.mm"
include "mpi.mm"
include "domtr.mm"
include "syl2anc.mm"
include "syl5eqbr.mm"

theorem abrexdom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  assume abrexdom.1: |- ( y e. A -> E* x ph )

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. V -> { x | E. y e. A ph } ~<_ A )

  proof
    cA
    cV
    wcel
    #
    wph
    vy
    cA
    wrex
    #
    vx
    cab
    #
    vy
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vy
    vx
    copab
    #
    crn
    #
    cA
    cdom
    @2
    @4
    vy
    wex
    #
    vx
    cab
    @6
    @1
    @7
    vx
    wph
    vy
    cA
    df-rex
    abbii
    @4
    vy
    vx
    rnopab
    eqtr4i
    @0
    @6
    @5
    cdm
    #
    cdom
    wbr
    #
    @8
    cA
    cdom
    wbr
    #
    @6
    cA
    cdom
    wbr
    @0
    @8
    cvv
    wcel
    #
    @5
    @8
    wfn
    #
    @9
    @8
    cA
    wss
    #
    @0
    @11
    wph
    vy
    vx
    cA
    dmopabss
    #
    @8
    cA
    cV
    ssexg
    mpan
    @0
    @5
    wfun
    #
    @12
    @15
    @0
    @15
    @4
    vx
    wmo
    #
    vy
    @4
    vy
    vx
    funopab
    @16
    @3
    wph
    vx
    wmo
    wi
    abrexdom.1
    @3
    wph
    vx
    moanimv
    mpbir
    mpgbir
    a1i
    @5
    funfn
    sylib
    @8
    cvv
    @5
    fnrndomg
    sylc
    @0
    @13
    @10
    @14
    @8
    cA
    cV
    ssdomg
    mpi
    @6
    @8
    cA
    domtr
    syl2anc
    syl5eqbr
end
