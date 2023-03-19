include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "creps.mm"
include "cshw1.mm"
include "wb.mm"
include "repswsymballbi.mm"
include "bicomd.mm"
include "adantr.mm"
include "mpbid.mm"

theorem cshw1repsw
  let cV: class V
  let cW: class W
  let vi: setvar i


  assert |- ( ( W e. Word V /\ ( W cyclShift 1 ) = W ) -> W = ( ( W ` 0 ) repeatS ( # ` W ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    c1
    ccsh
    co
    cW
    wceq
    #
    wa
    vi
    cv
    cW
    cfv
    cc0
    cW
    cfv
    #
    wceq
    vi
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    wral
    #
    cW
    @2
    @3
    creps
    co
    wceq
    #
    vi
    cV
    cW
    cshw1
    @0
    @4
    @5
    wb
    @1
    @0
    @5
    @4
    vi
    cV
    cW
    repswsymballbi
    bicomd
    adantr
    mpbid
end
