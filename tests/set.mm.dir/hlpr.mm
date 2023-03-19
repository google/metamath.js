include "chl.mm"
include "wcel.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "cdr.mm"
include "ccms.mm"
include "w3a.mm"
include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "hlprlem.mm"
include "eqid.mm"
include "cncdrg.mm"
include "syl.mm"

theorem hlpr
  let cF: class F
  let cK: class K
  let cW: class W
  assume hlress.f: |- F = ( Scalar ` W )
  assume hlress.k: |- K = ( Base ` F )


  assert |- ( W e. CHil -> K e. { RR , CC } )

  proof
    cW
    chl
    wcel
    cK
    ccnfld
    csubrg
    cfv
    wcel
    ccnfld
    cK
    cress
    co
    #
    cdr
    wcel
    @0
    ccms
    wcel
    w3a
    cK
    cr
    cc
    cpr
    wcel
    cF
    cK
    cW
    hlress.f
    hlress.k
    hlprlem
    @0
    cK
    @0
    eqid
    cncdrg
    syl
end
