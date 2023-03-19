include "wcel.mm"
include "cc0.mm"
include "crelexp.mm"
include "co.mm"
include "wrel.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "relres.mm"
include "relexp0g.mm"
include "releqd.mm"
include "mpbiri.mm"

theorem relexp0rel
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> Rel ( R ^r 0 ) )

  proof
    cR
    cV
    wcel
    #
    cR
    cc0
    crelexp
    co
    #
    wrel
    cid
    cR
    cdm
    cR
    crn
    cun
    #
    cres
    #
    wrel
    cid
    @2
    relres
    @0
    @1
    @3
    cR
    cV
    relexp0g
    releqd
    mpbiri
end
