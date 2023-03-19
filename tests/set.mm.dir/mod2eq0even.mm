include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cn.mm"
include "wb.mm"
include "2nn.mm"
include "dvdsval3.mm"
include "mpan.mm"
include "bicomd.mm"

theorem mod2eq0even
  let cN: class N


  assert |- ( N e. ZZ -> ( ( N mod 2 ) = 0 <-> 2 || N ) )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    #
    cN
    c2
    cmo
    co
    cc0
    wceq
    #
    c2
    cn
    wcel
    @0
    @1
    @2
    wb
    2nn
    c2
    cN
    dvdsval3
    mpan
    bicomd
end
