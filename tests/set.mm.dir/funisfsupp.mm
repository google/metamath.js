include "wfun.mm"
include "wcel.mm"
include "w3a.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wa.mm"
include "wb.mm"
include "isfsupp.mm"
include "3adant1.mm"
include "ibar.mm"
include "bicomd.mm"
include "3ad2ant1.mm"
include "bitrd.mm"

theorem funisfsupp
  let cR: class R
  let cV: class V
  let cW: class W
  let cZ: class Z


  assert |- ( ( Fun R /\ R e. V /\ Z e. W ) -> ( R finSupp Z <-> ( R supp Z ) e. Fin ) )

  proof
    cR
    wfun
    #
    cR
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    w3a
    cR
    cZ
    cfsupp
    wbr
    #
    @0
    cR
    cZ
    csupp
    co
    cfn
    wcel
    #
    wa
    #
    @4
    @1
    @2
    @3
    @5
    wb
    @0
    cR
    cV
    cW
    cZ
    isfsupp
    3adant1
    @0
    @1
    @5
    @4
    wb
    @2
    @0
    @4
    @5
    @0
    @4
    ibar
    bicomd
    3ad2ant1
    bitrd
end
