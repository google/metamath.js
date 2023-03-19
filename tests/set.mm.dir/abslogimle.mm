include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "cabs.mm"
include "cpi.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "cr.mm"
include "pire.mm"
include "a1i.mm"
include "renegcld.mm"
include "logcl.mm"
include "imcld.mm"
include "clt.mm"
include "logimcl.mm"
include "simpld.mm"
include "ltled.mm"
include "simprd.mm"
include "absled.mm"
include "mpbir2and.mm"

theorem abslogimle
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( abs ` ( Im ` ( log ` A ) ) ) <_ _pi )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    #
    cA
    clog
    cfv
    #
    cim
    cfv
    #
    cabs
    cfv
    cpi
    cle
    wbr
    cpi
    cneg
    #
    @2
    cle
    wbr
    @2
    cpi
    cle
    wbr
    #
    @0
    @3
    @2
    @0
    cpi
    cpi
    cr
    wcel
    @0
    pire
    a1i
    #
    renegcld
    @0
    @1
    cA
    logcl
    imcld
    #
    @0
    @3
    @2
    clt
    wbr
    #
    @4
    cA
    logimcl
    #
    simpld
    ltled
    @0
    @7
    @4
    @8
    simprd
    @0
    @2
    cpi
    @6
    @5
    absled
    mpbir2and
end
