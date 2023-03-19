include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "cc.mm"
include "wb.mm"
include "0cn.mm"
include "expeq0.mm"
include "mpan.mm"
include "mpbiri.mm"

theorem 0exp
  let cN: class N


  assert |- ( N e. NN -> ( 0 ^ N ) = 0 )

  proof
    cN
    cn
    wcel
    #
    cc0
    cN
    cexp
    co
    cc0
    wceq
    #
    cc0
    cc0
    wceq
    #
    cc0
    eqid
    cc0
    cc
    wcel
    @0
    @1
    @2
    wb
    0cn
    cc0
    cN
    expeq0
    mpan
    mpbiri
end
