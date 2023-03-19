include "crp.mm"
include "wcel.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cdiv.mm"
include "cz.mm"
include "c1.mm"
include "rpcn.mm"
include "rpne0.mm"
include "dividd.mm"
include "1z.mm"
include "syl6eqel.mm"
include "cr.mm"
include "wb.mm"
include "rpre.mm"
include "mod0.mm"
include "mpancom.mm"
include "mpbird.mm"

theorem modid0
  let cN: class N


  assert |- ( N e. RR+ -> ( N mod N ) = 0 )

  proof
    cN
    crp
    wcel
    #
    cN
    cN
    cmo
    co
    cc0
    wceq
    #
    cN
    cN
    cdiv
    co
    #
    cz
    wcel
    #
    @0
    @2
    c1
    cz
    @0
    cN
    cN
    rpcn
    cN
    rpne0
    dividd
    1z
    syl6eqel
    cN
    cr
    wcel
    @0
    @1
    @3
    wb
    cN
    rpre
    cN
    cN
    mod0
    mpancom
    mpbird
end
