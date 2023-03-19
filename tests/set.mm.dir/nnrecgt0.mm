include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "nnge1.mm"
include "0lt1.mm"
include "cr.mm"
include "wa.mm"
include "wi.mm"
include "nnre.mm"
include "0re.mm"
include "1re.mm"
include "ltletr.mm"
include "mp3an12.mm"
include "recgt0.mm"
include "ex.mm"
include "syld.mm"
include "syl.mm"
include "mpani.mm"
include "mpd.mm"

theorem nnrecgt0
  let cA: class A


  assert |- ( A e. NN -> 0 < ( 1 / A ) )

  proof
    cA
    cn
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    cc0
    c1
    cA
    cdiv
    co
    clt
    wbr
    #
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
    @0
    cA
    cr
    wcel
    #
    @3
    @1
    wa
    #
    @2
    wi
    cA
    nnre
    @4
    @5
    cc0
    cA
    clt
    wbr
    #
    @2
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @4
    @5
    @6
    wi
    0re
    1re
    cc0
    c1
    cA
    ltletr
    mp3an12
    @4
    @6
    @2
    cA
    recgt0
    ex
    syld
    syl
    mpani
    mpd
end
