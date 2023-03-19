include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "clt.mm"
include "nngt0.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "nnre.mm"
include "wa.mm"
include "ltnle.mm"
include "bicomd.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem nnnle0
  let cA: class A


  assert |- ( A e. NN -> -. A <_ 0 )

  proof
    cA
    cn
    wcel
    #
    cA
    cc0
    cle
    wbr
    wn
    #
    cc0
    cA
    clt
    wbr
    #
    cA
    nngt0
    @0
    cc0
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @1
    @2
    wb
    0re
    cA
    nnre
    @3
    @4
    wa
    @2
    @1
    cc0
    cA
    ltnle
    bicomd
    sylancr
    mpbird
end
