include "cn.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "wb.mm"
include "nnsub.mm"
include "mp2an.mm"

theorem nnsubi
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y
  assume nnsub.1: |- A e. NN
  assume nnsub.2: |- B e. NN


  assert |- ( A < B <-> ( B - A ) e. NN )

  proof
    cA
    cn
    wcel
    cB
    cn
    wcel
    cA
    cB
    clt
    wbr
    cB
    cA
    cmin
    co
    cn
    wcel
    wb
    nnsub.1
    nnsub.2
    cA
    cB
    nnsub
    mp2an
end
