include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "cpr.mm"
include "crelexp.mm"
include "co.mm"
include "ifid.mm"
include "eqcomi.mm"
include "jctr.mm"
include "c0ex.mm"
include "prid1.mm"
include "pm3.2i.mm"
include "relexp01min.mm"
include "sylancl.mm"

theorem relexp0idm
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( ( R ^r 0 ) ^r 0 ) = ( R ^r 0 ) )

  proof
    cR
    cV
    wcel
    #
    @0
    cc0
    cc0
    cc0
    clt
    wbr
    #
    cc0
    cc0
    cif
    #
    wceq
    #
    wa
    cc0
    cc0
    c1
    cpr
    wcel
    #
    @4
    wa
    cR
    cc0
    crelexp
    co
    #
    cc0
    crelexp
    co
    @5
    wceq
    @0
    @3
    @2
    cc0
    @1
    cc0
    ifid
    eqcomi
    jctr
    @4
    @4
    cc0
    c1
    c0ex
    prid1
    #
    @6
    pm3.2i
    cR
    cc0
    cc0
    cc0
    cV
    relexp01min
    sylancl
end
