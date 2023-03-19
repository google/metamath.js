include "csur.mm"
include "wcel.mm"
include "cbday.mm"
include "cfv.mm"
include "cdm.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "bdayval.mm"
include "word.mm"
include "nodmord.mm"
include "ordirr.mm"
include "syl.mm"
include "eqneltrd.mm"
include "ndmfv.mm"

theorem fvnobday
  let cA: class A


  assert |- ( A e. No -> ( A ` ( bday ` A ) ) = (/) )

  proof
    cA
    csur
    wcel
    #
    cA
    cbday
    cfv
    #
    cA
    cdm
    #
    wcel
    wn
    @1
    cA
    cfv
    c0
    wceq
    @0
    @1
    @2
    @2
    cA
    bdayval
    @0
    @2
    word
    @2
    @2
    wcel
    wn
    cA
    nodmord
    @2
    ordirr
    syl
    eqneltrd
    @1
    cA
    ndmfv
    syl
end
