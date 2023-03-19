include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cz.mm"
include "wcel.mm"
include "nnzi.mm"
include "nn0zi.mm"
include "dvdsmul1.mm"
include "mp2an.mm"
include "cn.mm"
include "clt.mm"
include "wa.mm"
include "wi.mm"
include "zmulcl.mm"
include "pm3.2i.mm"
include "ndvdsadd.mm"
include "mp3an.mm"
include "ax-mp.mm"
include "breq2i.mm"
include "mtbi.mm"

theorem ndvdsi
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  assume ndvdsi.1: |- A e. NN
  assume ndvdsi.2: |- Q e. NN0
  assume ndvdsi.3: |- R e. NN
  assume ndvdsi.4: |- ( ( A x. Q ) + R ) = B
  assume ndvdsi.5: |- R < A


  assert |- -. A || B

  proof
    cA
    cA
    cQ
    cmul
    co
    #
    cR
    caddc
    co
    #
    cdvds
    wbr
    #
    cA
    cB
    cdvds
    wbr
    cA
    @0
    cdvds
    wbr
    #
    @2
    wn
    #
    cA
    cz
    wcel
    #
    cQ
    cz
    wcel
    #
    @3
    cA
    ndvdsi.1
    nnzi
    #
    cQ
    ndvdsi.2
    nn0zi
    #
    cA
    cQ
    dvdsmul1
    mp2an
    @0
    cz
    wcel
    #
    cA
    cn
    wcel
    cR
    cn
    wcel
    #
    cR
    cA
    clt
    wbr
    #
    wa
    @3
    @4
    wi
    @5
    @6
    @9
    @7
    @8
    cA
    cQ
    zmulcl
    mp2an
    ndvdsi.1
    @10
    @11
    ndvdsi.3
    ndvdsi.5
    pm3.2i
    cA
    cR
    @0
    ndvdsadd
    mp3an
    ax-mp
    @1
    cB
    cA
    cdvds
    ndvdsi.4
    breq2i
    mtbi
end
