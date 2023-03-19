include "cmul.mm"
include "co.mm"
include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "eluz2b2.mm"
include "nprm.mm"
include "syl2anbr.mm"
include "mp4an.mm"
include "eleq1i.mm"
include "mtbi.mm"

theorem nprmi
  let cA: class A
  let cB: class B
  let cN: class N
  assume nprmi.1: |- A e. NN
  assume nprmi.2: |- B e. NN
  assume nprmi.3: |- 1 < A
  assume nprmi.4: |- 1 < B
  assume nprmi.5: |- ( A x. B ) = N


  assert |- -. N e. Prime

  proof
    cA
    cB
    cmul
    co
    #
    cprime
    wcel
    #
    cN
    cprime
    wcel
    cA
    cn
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    cB
    cn
    wcel
    #
    c1
    cB
    clt
    wbr
    #
    @1
    wn
    #
    nprmi.1
    nprmi.3
    nprmi.2
    nprmi.4
    @2
    @3
    wa
    cA
    c2
    cuz
    cfv
    #
    wcel
    cB
    @7
    wcel
    @6
    @4
    @5
    wa
    cA
    eluz2b2
    cB
    eluz2b2
    cA
    cB
    nprm
    syl2anbr
    mp4an
    @0
    cN
    cprime
    nprmi.5
    eleq1i
    mtbi
end
