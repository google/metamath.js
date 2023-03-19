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
include "wss.mm"
include "hlprlem.mm"
include "eqid.mm"
include "resscdrg.mm"
include "syl.mm"

theorem hlress
  let cF: class F
  let cK: class K
  let cW: class W
  assume hlress.f: |- F = ( Scalar ` W )
  assume hlress.k: |- K = ( Base ` F )


  assert |- ( W e. CHil -> RR C_ K )

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
    cr
    cK
    wss
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
    resscdrg
    syl
end
