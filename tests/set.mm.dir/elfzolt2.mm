include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "cz.mm"
include "wb.mm"
include "elfzoelz.mm"
include "elfzoel1.mm"
include "elfzoel2.mm"
include "elfzo.mm"
include "syl3anc.mm"
include "ibi.mm"
include "simprd.mm"

theorem elfzolt2
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) -> K < N )

  proof
    cK
    cM
    cN
    cfzo
    co
    wcel
    #
    cM
    cK
    cle
    wbr
    #
    cK
    cN
    clt
    wbr
    #
    @0
    @1
    @2
    wa
    #
    @0
    cK
    cz
    wcel
    cM
    cz
    wcel
    cN
    cz
    wcel
    @0
    @3
    wb
    cK
    cM
    cN
    elfzoelz
    cK
    cM
    cN
    elfzoel1
    cK
    cM
    cN
    elfzoel2
    cK
    cM
    cN
    elfzo
    syl3anc
    ibi
    simprd
end
