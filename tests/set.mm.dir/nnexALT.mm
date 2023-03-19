include "cn.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cima.mm"
include "df-nn.mm"
include "wfun.mm"
include "wcel.mm"
include "rdgfun.mm"
include "omex.mm"
include "funimaexg.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem nnexALT
  let vx: setvar x


  assert |- NN e. _V

  proof
    cn
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    #
    c1
    crdg
    #
    com
    cima
    #
    cvv
    vx
    df-nn
    @1
    wfun
    com
    cvv
    wcel
    @2
    cvv
    wcel
    c1
    @0
    rdgfun
    omex
    @1
    com
    cvv
    funimaexg
    mp2an
    eqeltri
end
