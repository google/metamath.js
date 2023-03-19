include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "nnre.mm"
include "nngt0.mm"
include "elrp.mm"
include "sylanbrc.mm"

theorem nnrp
  let cA: class A


  assert |- ( A e. NN -> A e. RR+ )

  proof
    cA
    cn
    wcel
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cA
    crp
    wcel
    cA
    nnre
    cA
    nngt0
    cA
    elrp
    sylanbrc
end
