include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cn.mm"
include "elfzolt2.mm"
include "cz.mm"
include "wb.mm"
include "elfzoelz.mm"
include "elfzoel2.mm"
include "znnsub.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem fzonnsub
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) -> ( N - K ) e. NN )

  proof
    cK
    cM
    cN
    cfzo
    co
    wcel
    #
    cK
    cN
    clt
    wbr
    #
    cN
    cK
    cmin
    co
    cn
    wcel
    #
    cK
    cM
    cN
    elfzolt2
    @0
    cK
    cz
    wcel
    cN
    cz
    wcel
    @1
    @2
    wb
    cK
    cM
    cN
    elfzoelz
    cK
    cM
    cN
    elfzoel2
    cK
    cN
    znnsub
    syl2anc
    mpbid
end
