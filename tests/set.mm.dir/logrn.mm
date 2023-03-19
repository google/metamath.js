include "clog.mm"
include "crn.mm"
include "ce.mm"
include "cim.mm"
include "ccnv.mm"
include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "cima.mm"
include "cres.mm"
include "df-log.mm"
include "rneqi.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wf1o.mm"
include "wfo.mm"
include "wceq.mm"
include "eqid.mm"
include "eff1o.mm"
include "f1ocnv.mm"
include "ax-mp.mm"
include "f1ofo.mm"
include "forn.mm"
include "mp2b.mm"
include "eqtri.mm"

theorem logrn



  assert |- ran log = ( `' Im " ( -u _pi (,] _pi ) )

  proof
    clog
    crn
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
    #
    crn
    #
    @0
    clog
    @2
    df-log
    rneqi
    cc
    cc0
    csn
    cdif
    #
    @0
    @2
    wf1o
    #
    @4
    @0
    @2
    wfo
    @3
    @0
    wceq
    @0
    @4
    @1
    wf1o
    @5
    @0
    @0
    eqid
    eff1o
    @0
    @4
    @1
    f1ocnv
    ax-mp
    @4
    @0
    @2
    f1ofo
    @4
    @0
    @2
    forn
    mp2b
    eqtri
end
