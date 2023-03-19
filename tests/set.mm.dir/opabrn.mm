include "copab.mm"
include "wceq.mm"
include "crn.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "dfrn2.mm"
include "nfopab2.mm"
include "nfeq2.mm"
include "nfopab1.mm"
include "cop.mm"
include "wcel.mm"
include "df-br.mm"
include "eleq2.mm"
include "opabid.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "exbid.mm"
include "abbid.mm"
include "syl5eq.mm"

theorem opabrn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint x y
  disjoint R x
  disjoint R y
  assert |- ( R = { <. x , y >. | ph } -> ran R = { y | E. x ph } )

  proof
    cR
    wph
    vx
    vy
    copab
    #
    wceq
    #
    cR
    crn
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vx
    wex
    #
    vy
    cab
    wph
    vx
    wex
    #
    vy
    cab
    vx
    vy
    cR
    dfrn2
    @1
    @5
    @6
    vy
    vy
    cR
    @0
    wph
    vx
    vy
    nfopab2
    nfeq2
    @1
    @4
    wph
    vx
    vx
    cR
    @0
    wph
    vx
    vy
    nfopab1
    nfeq2
    @4
    @2
    @3
    cop
    #
    cR
    wcel
    #
    @1
    wph
    @2
    @3
    cR
    df-br
    @1
    @8
    @7
    @0
    wcel
    wph
    cR
    @0
    @7
    eleq2
    wph
    vx
    vy
    opabid
    syl6bb
    syl5bb
    exbid
    abbid
    syl5eq
end
