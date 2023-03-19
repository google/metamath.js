include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "peano2zm.mm"
include "ad2antrl.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "1re.mm"
include "leaddsub.mm"
include "mp3an2.mm"
include "syl2an.mm"
include "biimpa.mm"
include "anasss.mm"
include "jca.mm"
include "ex.mm"
include "peano2z.mm"
include "eluz1.mm"
include "syl.mm"
include "3imtr4d.mm"
include "imp.mm"

theorem eluzp1m1
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ( ZZ>= ` ( M + 1 ) ) ) -> ( N - 1 ) e. ( ZZ>= ` M ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cM
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    cN
    c1
    cmin
    co
    #
    cM
    cuz
    cfv
    wcel
    #
    @0
    cN
    cz
    wcel
    #
    @1
    cN
    cle
    wbr
    #
    wa
    #
    @3
    cz
    wcel
    #
    cM
    @3
    cle
    wbr
    #
    wa
    #
    @2
    @4
    @0
    @7
    @10
    @0
    @7
    wa
    @8
    @9
    @5
    @8
    @0
    @6
    cN
    peano2zm
    ad2antrl
    @0
    @5
    @6
    @9
    @0
    @5
    wa
    @6
    @9
    @0
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @6
    @9
    wb
    #
    @5
    cM
    zre
    cN
    zre
    @11
    c1
    cr
    wcel
    @12
    @13
    1re
    cM
    c1
    cN
    leaddsub
    mp3an2
    syl2an
    biimpa
    anasss
    jca
    ex
    @0
    @1
    cz
    wcel
    @2
    @7
    wb
    cM
    peano2z
    @1
    cN
    eluz1
    syl
    cM
    @3
    eluz1
    3imtr4d
    imp
end
