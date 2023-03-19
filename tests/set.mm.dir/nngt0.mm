include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "clt.mm"
include "nnre.mm"
include "nnge1.mm"
include "0lt1.mm"
include "wa.mm"
include "wi.mm"
include "0re.mm"
include "1re.mm"
include "ltletr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "sylc.mm"

theorem nngt0
  let cA: class A


  assert |- ( A e. NN -> 0 < A )

  proof
    cA
    cn
    wcel
    cA
    cr
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    cc0
    cA
    clt
    wbr
    #
    cA
    nnre
    cA
    nnge1
    @0
    cc0
    c1
    clt
    wbr
    #
    @1
    @2
    0lt1
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @0
    @3
    @1
    wa
    @2
    wi
    0re
    1re
    cc0
    c1
    cA
    ltletr
    mp3an12
    mpani
    sylc
end
