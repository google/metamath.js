include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "nnge1.mm"
include "biantrud.mm"
include "cr.mm"
include "wb.mm"
include "nnre.mm"
include "1re.mm"
include "letri3.mm"
include "sylancl.mm"
include "bitr4d.mm"

theorem nnle1eq1
  let cA: class A


  assert |- ( A e. NN -> ( A <_ 1 <-> A = 1 ) )

  proof
    cA
    cn
    wcel
    #
    cA
    c1
    cle
    wbr
    #
    @1
    c1
    cA
    cle
    wbr
    #
    wa
    #
    cA
    c1
    wceq
    #
    @0
    @2
    @1
    cA
    nnge1
    biantrud
    @0
    cA
    cr
    wcel
    c1
    cr
    wcel
    @4
    @3
    wb
    cA
    nnre
    1re
    cA
    c1
    letri3
    sylancl
    bitr4d
end
