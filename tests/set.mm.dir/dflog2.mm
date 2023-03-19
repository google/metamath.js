include "clog.mm"
include "ce.mm"
include "cim.mm"
include "ccnv.mm"
include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "df-log.mm"
include "logrn.mm"
include "reseq2i.mm"
include "cnveqi.mm"
include "eqtr4i.mm"

theorem dflog2



  assert |- log = `' ( exp |` ran log )

  proof
    clog
    ce
    cim
    ccnv
    cpi
    cneg
    cpi
    cioc
    co
    cima
    #
    cres
    #
    ccnv
    ce
    clog
    crn
    #
    cres
    #
    ccnv
    df-log
    @3
    @1
    @2
    @0
    ce
    logrn
    reseq2i
    cnveqi
    eqtr4i
end
