include "cz.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cmin.mm"
include "simpr.mm"
include "wb.mm"
include "elfzel1.mm"
include "adantl.mm"
include "elfzel2.mm"
include "simpl.mm"
include "elfzelz.mm"
include "fzrev2.mm"
include "syl22anc.mm"
include "mpbid.mm"

theorem fzrev2i
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( J e. ZZ /\ K e. ( M ... N ) ) -> ( J - K ) e. ( ( J - N ) ... ( J - M ) ) )

  proof
    cJ
    cz
    wcel
    #
    cK
    cM
    cN
    cfz
    co
    wcel
    #
    wa
    #
    @1
    cJ
    cK
    cmin
    co
    cJ
    cN
    cmin
    co
    cJ
    cM
    cmin
    co
    cfz
    co
    wcel
    #
    @0
    @1
    simpr
    @2
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @0
    cK
    cz
    wcel
    #
    @1
    @3
    wb
    @1
    @4
    @0
    cK
    cM
    cN
    elfzel1
    adantl
    @1
    @5
    @0
    cK
    cM
    cN
    elfzel2
    adantl
    @0
    @1
    simpl
    @1
    @6
    @0
    cK
    cM
    cN
    elfzelz
    adantl
    cJ
    cK
    cM
    cN
    fzrev2
    syl22anc
    mpbid
end
