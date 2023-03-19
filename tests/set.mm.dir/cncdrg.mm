include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cdr.mm"
include "ccms.mm"
include "w3a.mm"
include "cr.mm"
include "wss.mm"
include "cc.mm"
include "cpr.mm"
include "simp1.mm"
include "resscdrg.mm"
include "cnsubrg.mm"
include "syl2anc.mm"

theorem cncdrg
  let cF: class F
  let cK: class K
  assume resscdrg.1: |- F = ( CCfld |`s K )


  assert |- ( ( K e. ( SubRing ` CCfld ) /\ F e. DivRing /\ F e. CMetSp ) -> K e. { RR , CC } )

  proof
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    cF
    cdr
    wcel
    #
    cF
    ccms
    wcel
    #
    w3a
    @0
    cr
    cK
    wss
    cK
    cr
    cc
    cpr
    wcel
    @0
    @1
    @2
    simp1
    cF
    cK
    resscdrg.1
    resscdrg
    cK
    cnsubrg
    syl2anc
end
