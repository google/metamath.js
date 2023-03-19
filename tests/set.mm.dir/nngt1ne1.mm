include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wne.mm"
include "wb.mm"
include "nnre.mm"
include "nnge1.mm"
include "1re.mm"
include "leltne.mm"
include "mp3an1.mm"
include "syl2anc.mm"

theorem nngt1ne1
  let cA: class A


  assert |- ( A e. NN -> ( 1 < A <-> A =/= 1 ) )

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
    c1
    cA
    clt
    wbr
    cA
    c1
    wne
    wb
    #
    cA
    nnre
    cA
    nnge1
    c1
    cr
    wcel
    @0
    @1
    @2
    1re
    c1
    cA
    leltne
    mp3an1
    syl2anc
end
