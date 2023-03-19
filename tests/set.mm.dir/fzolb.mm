include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "elfzo2.mm"
include "eluzel2.mm"
include "uzid.mm"
include "impbii.mm"
include "3anbi1i.mm"
include "bitri.mm"

theorem fzolb
  let cM: class M
  let cN: class N


  assert |- ( M e. ( M ..^ N ) <-> ( M e. ZZ /\ N e. ZZ /\ M < N ) )

  proof
    cM
    cM
    cN
    cfzo
    co
    wcel
    cM
    cM
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cN
    clt
    wbr
    #
    w3a
    cM
    cz
    wcel
    #
    @1
    @2
    w3a
    cM
    cM
    cN
    elfzo2
    @0
    @3
    @1
    @2
    @0
    @3
    cM
    cM
    eluzel2
    cM
    uzid
    impbii
    3anbi1i
    bitri
end
