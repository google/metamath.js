include "cfz.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "elfzuz2.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "eluzfz1.mm"
include "ne0i.mm"
include "syl.mm"
include "impbii.mm"

theorem fzn0
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( M ... N ) =/= (/) <-> N e. ( ZZ>= ` M ) )

  proof
    cM
    cN
    cfz
    co
    #
    c0
    wne
    #
    cN
    cM
    cuz
    cfv
    wcel
    #
    @1
    vx
    cv
    #
    @0
    wcel
    #
    vx
    wex
    @2
    vx
    @0
    n0
    @4
    @2
    vx
    @3
    cM
    cN
    elfzuz2
    exlimiv
    sylbi
    @2
    cM
    @0
    wcel
    @1
    cM
    cN
    eluzfz1
    @0
    cM
    ne0i
    syl
    impbii
end
