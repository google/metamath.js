include "crp.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "cdiv.mm"
include "cz.mm"
include "2cnd.mm"
include "rpcn.mm"
include "rpne0.mm"
include "divcan4d.mm"
include "2z.mm"
include "syl6eqel.mm"
include "cr.mm"
include "wb.mm"
include "2re.mm"
include "a1i.mm"
include "rpre.mm"
include "remulcld.mm"
include "mod0.mm"
include "mpancom.mm"
include "mpbird.mm"

theorem 2txmodxeq0
  let cX: class X


  assert |- ( X e. RR+ -> ( ( 2 x. X ) mod X ) = 0 )

  proof
    cX
    crp
    wcel
    #
    c2
    cX
    cmul
    co
    #
    cX
    cmo
    co
    cc0
    wceq
    #
    @1
    cX
    cdiv
    co
    #
    cz
    wcel
    #
    @0
    @3
    c2
    cz
    @0
    c2
    cX
    @0
    2cnd
    cX
    rpcn
    cX
    rpne0
    divcan4d
    2z
    syl6eqel
    @1
    cr
    wcel
    @0
    @2
    @4
    wb
    @0
    c2
    cX
    c2
    cr
    wcel
    @0
    2re
    a1i
    cX
    rpre
    remulcld
    @1
    cX
    mod0
    mpancom
    mpbird
end
