include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wb.mm"
include "simpl.mm"
include "zsubcl.mm"
include "jca.mm"
include "fzrev.mm"
include "sylan2.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "nncan.mm"
include "syl2an.mm"
include "adantl.mm"
include "eleq1d.mm"
include "bitr2d.mm"

theorem fzrev2
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ ( J e. ZZ /\ K e. ZZ ) ) -> ( K e. ( M ... N ) <-> ( J - K ) e. ( ( J - N ) ... ( J - M ) ) ) )

  proof
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    #
    cJ
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    wa
    #
    cJ
    cK
    cmin
    co
    #
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
    cJ
    @5
    cmin
    co
    #
    cM
    cN
    cfz
    co
    #
    wcel
    #
    cK
    @8
    wcel
    @3
    @0
    @1
    @5
    cz
    wcel
    #
    wa
    @6
    @9
    wb
    @3
    @1
    @10
    @1
    @2
    simpl
    cJ
    cK
    zsubcl
    jca
    cJ
    @5
    cM
    cN
    fzrev
    sylan2
    @4
    @7
    cK
    @8
    @3
    @7
    cK
    wceq
    #
    @0
    @1
    cJ
    cc
    wcel
    cK
    cc
    wcel
    @11
    @2
    cJ
    zcn
    cK
    zcn
    cJ
    cK
    nncan
    syl2an
    adantl
    eleq1d
    bitr2d
end
