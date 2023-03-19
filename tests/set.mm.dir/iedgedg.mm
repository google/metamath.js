include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "crn.mm"
include "cedg.mm"
include "fvelrn.mm"
include "ciedg.mm"
include "edgval.mm"
include "rneqi.mm"
include "eqtr4i.mm"
include "syl6eleqr.mm"

theorem iedgedg
  let cE: class E
  let cG: class G
  let cI: class I
  assume iedgedg.e: |- E = ( iEdg ` G )


  assert |- ( ( Fun E /\ I e. dom E ) -> ( E ` I ) e. ( Edg ` G ) )

  proof
    cE
    wfun
    cI
    cE
    cdm
    wcel
    wa
    cI
    cE
    cfv
    cE
    crn
    #
    cG
    cedg
    cfv
    #
    cI
    cE
    fvelrn
    @1
    cG
    ciedg
    cfv
    #
    crn
    @0
    cG
    edgval
    cE
    @2
    iedgedg.e
    rneqi
    eqtr4i
    syl6eleqr
end
