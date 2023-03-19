include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "cle.mm"
include "elfzolt2.mm"
include "cz.mm"
include "wb.mm"
include "elfzoelz.mm"
include "elfzoel2.mm"
include "zltp1le.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem elfzop1le2
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) -> ( K + 1 ) <_ N )

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
    cK
    c1
    caddc
    co
    cN
    cle
    wbr
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
    zltp1le
    syl2anc
    mpbid
end
