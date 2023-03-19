include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "cfzo.mm"
include "co.mm"
include "3anass.mm"
include "elfzo2.mm"
include "wb.mm"
include "eluzelz.mm"
include "fzolb.mm"
include "bitri.mm"
include "baib.mm"
include "syl.mm"
include "pm5.32i.mm"
include "3bitr4i.mm"

theorem elfzo3
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) <-> ( K e. ( ZZ>= ` M ) /\ K e. ( K ..^ N ) ) )

  proof
    cK
    cM
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cN
    clt
    wbr
    #
    w3a
    @0
    @1
    @2
    wa
    #
    wa
    cK
    cM
    cN
    cfzo
    co
    wcel
    @0
    cK
    cK
    cN
    cfzo
    co
    wcel
    #
    wa
    @0
    @1
    @2
    3anass
    cK
    cM
    cN
    elfzo2
    @0
    @4
    @3
    @0
    cK
    cz
    wcel
    #
    @4
    @3
    wb
    cM
    cK
    eluzelz
    @4
    @5
    @3
    @4
    @5
    @1
    @2
    w3a
    @5
    @3
    wa
    cK
    cN
    fzolb
    @5
    @1
    @2
    3anass
    bitri
    baib
    syl
    pm5.32i
    3bitr4i
end
