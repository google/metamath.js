include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "hl2at.mm"
include "wa.mm"
include "df-rex.mm"
include "exsimpl.mm"
include "sylbi.mm"
include "syl.mm"
include "n0.mm"
include "sylibr.mm"

theorem atex
  let cA: class A
  let cK: class K
  let vp: setvar p
  let vq: setvar q
  assume atex.1: |- A = ( Atoms ` K )


  assert |- ( K e. HL -> A =/= (/) )

  proof
    cK
    chlt
    wcel
    #
    vp
    cv
    #
    cA
    wcel
    #
    vp
    wex
    #
    cA
    c0
    wne
    @0
    @1
    vq
    cv
    wne
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    #
    @3
    cA
    cK
    vq
    vp
    atex.1
    hl2at
    @5
    @2
    @4
    wa
    vp
    wex
    @3
    @4
    vp
    cA
    df-rex
    @2
    @4
    vp
    exsimpl
    sylbi
    syl
    vp
    cA
    n0
    sylibr
end
