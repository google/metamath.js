include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "cfusgr.mm"
include "cclwwlkn.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "prmnn.mm"
include "clwwlkndivn.mm"
include "dvdsmod0.mm"
include "syl2an2.mm"

theorem numclwwlk8
  let cP: class P
  let cG: class G


  assert |- ( ( G e. FinUSGraph /\ P e. Prime ) -> ( ( # ` ( P ClWWalksN G ) ) mod P ) = 0 )

  proof
    cP
    cprime
    wcel
    cP
    cn
    wcel
    cG
    cfusgr
    wcel
    cP
    cP
    cG
    cclwwlkn
    co
    chash
    cfv
    #
    cdvds
    wbr
    @0
    cP
    cmo
    co
    cc0
    wceq
    cP
    prmnn
    cG
    cP
    clwwlkndivn
    cP
    @0
    dvdsmod0
    syl2an2
end
