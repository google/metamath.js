include "cusgr.mm"
include "wcel.mm"
include "cdm.mm"
include "crn.mm"
include "wf1o.mm"
include "wf1.mm"
include "usgrf1o.mm"
include "f1of1.mm"
include "syl.mm"

theorem usgrf1
  let cE: class E
  let cG: class G
  let vx: setvar x
  assume usgrf1o.e: |- E = ( iEdg ` G )


  assert |- ( G e. USGraph -> E : dom E -1-1-> ran E )

  proof
    cG
    cusgr
    wcel
    cE
    cdm
    #
    cE
    crn
    #
    cE
    wf1o
    @0
    @1
    cE
    wf1
    cE
    cG
    usgrf1o.e
    usgrf1o
    @0
    @1
    cE
    f1of1
    syl
end
