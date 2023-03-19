include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cdv.mm"
include "co.mm"
include "crg.mm"
include "cnring.mm"
include "cnfldbas.mm"
include "subrgid.mm"
include "ax-mp.mm"
include "plyssc.mm"
include "sseli.mm"
include "dvply2g.mm"
include "sylancr.mm"

theorem dvply2
  let cS: class S
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( F e. ( Poly ` S ) -> ( CC _D F ) e. ( Poly ` CC ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    cc
    ccnfld
    csubrg
    cfv
    wcel
    #
    cF
    cc
    cply
    cfv
    #
    wcel
    cc
    cF
    cdv
    co
    @2
    wcel
    ccnfld
    crg
    wcel
    @1
    cnring
    cc
    ccnfld
    cnfldbas
    subrgid
    ax-mp
    @0
    @2
    cF
    cS
    plyssc
    sseli
    cc
    cF
    dvply2g
    sylancr
end
