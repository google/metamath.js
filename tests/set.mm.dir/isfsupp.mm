include "cv.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cfsupp.mm"
include "wceq.mm"
include "wb.mm"
include "funeq.mm"
include "adantr.mm"
include "oveq12.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "df-fsupp.mm"
include "brabga.mm"

theorem isfsupp
  let cR: class R
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vr: setvar r
  let vz: setvar z


  assert |- ( ( R e. V /\ Z e. W ) -> ( R finSupp Z <-> ( Fun R /\ ( R supp Z ) e. Fin ) ) )

  proof
    vr
    cv
    #
    wfun
    #
    @0
    vz
    cv
    #
    csupp
    co
    #
    cfn
    wcel
    #
    wa
    cR
    wfun
    #
    cR
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    wa
    vr
    vz
    cR
    cZ
    cfsupp
    cV
    cW
    @0
    cR
    wceq
    #
    @2
    cZ
    wceq
    #
    wa
    #
    @1
    @5
    @4
    @7
    @8
    @1
    @5
    wb
    @9
    @0
    cR
    funeq
    adantr
    @10
    @3
    @6
    cfn
    @0
    cR
    @2
    cZ
    csupp
    oveq12
    eleq1d
    anbi12d
    vz
    vr
    df-fsupp
    brabga
end
