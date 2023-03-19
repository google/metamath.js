include "c1o.mm"
include "csuc.mm"
include "c2o.mm"
include "cuni.mm"
include "wceq.mm"
include "df-2o.mm"
include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wlim.mm"
include "wn.mm"
include "2on.mm"
include "2on0.mm"
include "com.mm"
include "2onn.mm"
include "nnlim.mm"
include "ax-mp.mm"
include "onsucuni3.mm"
include "mp3an.mm"
include "eqtr3i.mm"
include "suc11reg.mm"
include "mpbi.mm"

theorem 1oequni2o



  assert |- 1o = U. 2o

  proof
    c1o
    csuc
    #
    c2o
    cuni
    #
    csuc
    #
    wceq
    c1o
    @1
    wceq
    c2o
    @0
    @2
    df-2o
    c2o
    con0
    wcel
    c2o
    c0
    wne
    c2o
    wlim
    wn
    #
    c2o
    @2
    wceq
    2on
    2on0
    c2o
    com
    wcel
    @3
    2onn
    c2o
    nnlim
    ax-mp
    c2o
    onsucuni3
    mp3an
    eqtr3i
    c1o
    @1
    suc11reg
    mpbi
end
