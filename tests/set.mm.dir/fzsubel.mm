include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "cneg.mm"
include "caddc.mm"
include "cmin.mm"
include "wb.mm"
include "znegcl.mm"
include "fzaddel.mm"
include "sylanr2.mm"
include "cc.mm"
include "zcn.mm"
include "anim12i.mm"
include "wceq.mm"
include "negsub.mm"
include "adantl.mm"
include "oveqan12d.mm"
include "anandirs.mm"
include "adantrl.mm"
include "eleq12d.mm"
include "syl2an.mm"
include "bitrd.mm"

theorem fzsubel
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ ( J e. ZZ /\ K e. ZZ ) ) -> ( J e. ( M ... N ) <-> ( J - K ) e. ( ( M - K ) ... ( N - K ) ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
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
    cJ
    cM
    cN
    cfz
    co
    wcel
    #
    cJ
    cK
    cneg
    #
    caddc
    co
    #
    cM
    @7
    caddc
    co
    #
    cN
    @7
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    cJ
    cK
    cmin
    co
    #
    cM
    cK
    cmin
    co
    #
    cN
    cK
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    @4
    @2
    @3
    @7
    cz
    wcel
    @6
    @12
    wb
    cK
    znegcl
    cJ
    @7
    cM
    cN
    fzaddel
    sylanr2
    @2
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    wa
    #
    cJ
    cc
    wcel
    #
    cK
    cc
    wcel
    #
    wa
    #
    @12
    @17
    wb
    @5
    @0
    @18
    @1
    @19
    cM
    zcn
    cN
    zcn
    anim12i
    @3
    @21
    @4
    @22
    cJ
    zcn
    cK
    zcn
    anim12i
    @20
    @23
    wa
    @8
    @13
    @11
    @16
    @23
    @8
    @13
    wceq
    @20
    cJ
    cK
    negsub
    adantl
    @20
    @22
    @11
    @16
    wceq
    #
    @21
    @18
    @19
    @22
    @24
    @18
    @22
    wa
    @19
    @22
    wa
    @9
    @14
    @10
    @15
    cfz
    cM
    cK
    negsub
    cN
    cK
    negsub
    oveqan12d
    anandirs
    adantrl
    eleq12d
    syl2an
    bitrd
end
