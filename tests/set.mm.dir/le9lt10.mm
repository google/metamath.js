include "c9.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "cdc.mm"
include "clt.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "wcel.mm"
include "wb.mm"
include "nn0zi.mm"
include "9nn0.mm"
include "zleltp1.mm"
include "mp2an.mm"
include "mpbi.mm"
include "9p1e10.mm"
include "breqtri.mm"

theorem le9lt10
  let cA: class A
  assume le9lt10.c: |- A e. NN0
  assume le9lt10.e: |- A <_ 9


  assert |- A < ; 1 0

  proof
    cA
    c9
    c1
    caddc
    co
    #
    c1
    cc0
    cdc
    clt
    cA
    c9
    cle
    wbr
    #
    cA
    @0
    clt
    wbr
    #
    le9lt10.e
    cA
    cz
    wcel
    c9
    cz
    wcel
    @1
    @2
    wb
    cA
    le9lt10.c
    nn0zi
    c9
    9nn0
    nn0zi
    cA
    c9
    zleltp1
    mp2an
    mpbi
    9p1e10
    breqtri
end
