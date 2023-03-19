include "cz.mm"
include "cmin.mm"
include "cn.mm"
include "cxp.mm"
include "cima.mm"
include "cvv.mm"
include "dfz2.mm"
include "cc.mm"
include "wf.mm"
include "wfun.mm"
include "wcel.mm"
include "subf.mm"
include "ffun.mm"
include "nnexALT.mm"
include "xpex.mm"
include "funimaex.mm"
include "mp2b.mm"
include "eqeltri.mm"

theorem zexALT



  assert |- ZZ e. _V

  proof
    cz
    cmin
    cn
    cn
    cxp
    #
    cima
    #
    cvv
    dfz2
    cc
    cc
    cxp
    #
    cc
    cmin
    wf
    cmin
    wfun
    @1
    cvv
    wcel
    subf
    @2
    cc
    cmin
    ffun
    cmin
    @0
    cn
    cn
    nnexALT
    nnexALT
    xpex
    funimaex
    mp2b
    eqeltri
end
