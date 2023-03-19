include "cle.mm"
include "cuni.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cxr.mm"
include "wrel.mm"
include "wceq.mm"
include "lerel.mm"
include "relfld.mm"
include "ax-mp.mm"
include "ledm.mm"
include "lern.mm"
include "uneq12i.mm"
include "unidm.mm"
include "3eqtr2ri.mm"

theorem lefld



  assert |- RR* = U. U. <_

  proof
    cle
    cuni
    cuni
    #
    cle
    cdm
    #
    cle
    crn
    #
    cun
    #
    cxr
    cxr
    cun
    cxr
    cle
    wrel
    @0
    @3
    wceq
    lerel
    cle
    relfld
    ax-mp
    cxr
    @1
    cxr
    @2
    ledm
    lern
    uneq12i
    cxr
    unidm
    3eqtr2ri
end
