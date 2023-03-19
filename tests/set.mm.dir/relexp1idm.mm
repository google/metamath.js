include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cpr.mm"
include "crelexp.mm"
include "co.mm"
include "ifid.mm"
include "eqcomi.mm"
include "jctr.mm"
include "1ex.mm"
include "prid2.mm"
include "pm3.2i.mm"
include "relexp01min.mm"
include "sylancl.mm"

theorem relexp1idm
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( ( R ^r 1 ) ^r 1 ) = ( R ^r 1 ) )

  proof
    cR
    cV
    wcel
    #
    @0
    c1
    c1
    c1
    clt
    wbr
    #
    c1
    c1
    cif
    #
    wceq
    #
    wa
    c1
    cc0
    c1
    cpr
    wcel
    #
    @4
    wa
    cR
    c1
    crelexp
    co
    #
    c1
    crelexp
    co
    @5
    wceq
    @0
    @3
    @2
    c1
    @1
    c1
    ifid
    eqcomi
    jctr
    @4
    @4
    cc0
    c1
    1ex
    prid2
    #
    @6
    pm3.2i
    cR
    c1
    c1
    c1
    cV
    relexp01min
    sylancl
end
