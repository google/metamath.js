include "cc0.mm"
include "cpnf.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "c0.mm"
include "noel.mm"
include "cz.mm"
include "wa.mm"
include "wn.mm"
include "wceq.mm"
include "cxr.mm"
include "pnfxr.mm"
include "xrltnr.mm"
include "ax-mp.mm"
include "cr.mm"
include "zre.mm"
include "ltpnf.mm"
include "syl.mm"
include "mto.mm"
include "intnan.mm"
include "cxp.mm"
include "cpw.mm"
include "fzf.mm"
include "fdmi.mm"
include "ndmov.mm"
include "eleq2i.mm"
include "mtbir.mm"
include "pm2.21i.mm"

theorem topnfbey
  let cB: class B


  assert |- ( B e. ( 0 ... +oo ) -> +oo < B )

  proof
    cB
    cc0
    cpnf
    cfz
    co
    #
    wcel
    #
    cpnf
    cB
    clt
    wbr
    @1
    cB
    c0
    wcel
    cB
    noel
    @0
    c0
    cB
    cc0
    cz
    wcel
    #
    cpnf
    cz
    wcel
    #
    wa
    wn
    @0
    c0
    wceq
    @3
    @2
    @3
    cpnf
    cpnf
    clt
    wbr
    #
    cpnf
    cxr
    wcel
    @4
    wn
    pnfxr
    cpnf
    xrltnr
    ax-mp
    @3
    cpnf
    cr
    wcel
    @4
    cpnf
    zre
    cpnf
    ltpnf
    syl
    mto
    intnan
    cc0
    cpnf
    cz
    cfz
    cz
    cz
    cxp
    cz
    cpw
    cfz
    fzf
    fdmi
    ndmov
    ax-mp
    eleq2i
    mtbir
    pm2.21i
end
