include "cnpi.mm"
include "wcel.mm"
include "c1o.mm"
include "clti.mm"
include "wbr.mm"
include "wn.mm"
include "c0.mm"
include "wne.mm"
include "com.mm"
include "elni.mm"
include "simprbi.mm"
include "wceq.mm"
include "wa.mm"
include "noel.mm"
include "wo.mm"
include "wb.mm"
include "1pi.mm"
include "ltpiord.mm"
include "mpan2.mm"
include "csuc.mm"
include "df-1o.mm"
include "eleq2i.mm"
include "elsucg.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "biimpa.mm"
include "ord.mm"
include "mpi.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"
include "ltrelpi.mm"
include "brel.mm"
include "simpld.mm"
include "con3i.mm"
include "pm2.61i.mm"

theorem nlt1pi
  let cA: class A


  assert |- -. A <N 1o

  proof
    cA
    cnpi
    wcel
    #
    cA
    c1o
    clti
    wbr
    #
    wn
    #
    @0
    cA
    c0
    wne
    #
    @2
    @0
    cA
    com
    wcel
    @3
    cA
    elni
    simprbi
    @0
    @1
    cA
    c0
    @0
    @1
    cA
    c0
    wceq
    #
    @0
    @1
    wa
    #
    cA
    c0
    wcel
    #
    wn
    @4
    cA
    noel
    @5
    @6
    @4
    @0
    @1
    @6
    @4
    wo
    #
    @0
    @1
    cA
    c1o
    wcel
    #
    @7
    @0
    c1o
    cnpi
    wcel
    #
    @1
    @8
    wb
    1pi
    cA
    c1o
    ltpiord
    mpan2
    @8
    cA
    c0
    csuc
    #
    wcel
    @0
    @7
    c1o
    @10
    cA
    df-1o
    eleq2i
    cA
    c0
    cnpi
    elsucg
    syl5bb
    bitrd
    biimpa
    ord
    mpi
    ex
    necon3ad
    mpd
    @1
    @0
    @1
    @0
    @9
    cA
    c1o
    cnpi
    cnpi
    clti
    ltrelpi
    brel
    simpld
    con3i
    pm2.61i
end
