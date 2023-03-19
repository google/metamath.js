include "crp.mm"
include "wcel.mm"
include "cc0.mm"
include "cr.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "0re.mm"
include "jctl.mm"
include "rpgt0.mm"
include "0le0.mm"
include "jctil.mm"
include "modid.mm"
include "syl2anc.mm"

theorem 0mod
  let cN: class N


  assert |- ( N e. RR+ -> ( 0 mod N ) = 0 )

  proof
    cN
    crp
    wcel
    #
    cc0
    cr
    wcel
    #
    @0
    wa
    cc0
    cc0
    cle
    wbr
    #
    cc0
    cN
    clt
    wbr
    #
    wa
    cc0
    cN
    cmo
    co
    cc0
    wceq
    @0
    @1
    0re
    jctl
    @0
    @3
    @2
    cN
    rpgt0
    0le0
    jctil
    cc0
    cN
    modid
    syl2anc
end
