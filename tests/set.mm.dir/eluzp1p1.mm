include "cz.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "peano2z.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "1re.mm"
include "leadd1.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "biimp3a.mm"
include "3jca.mm"
include "eluz2.mm"
include "3imtr4i.mm"

theorem eluzp1p1
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( N + 1 ) e. ( ZZ>= ` ( M + 1 ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    w3a
    #
    cM
    c1
    caddc
    co
    #
    cz
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cz
    wcel
    #
    @4
    @6
    cle
    wbr
    #
    w3a
    cN
    cM
    cuz
    cfv
    wcel
    @6
    @4
    cuz
    cfv
    wcel
    @3
    @5
    @7
    @8
    @0
    @1
    @5
    @2
    cM
    peano2z
    3ad2ant1
    @1
    @0
    @7
    @2
    cN
    peano2z
    3ad2ant2
    @0
    @1
    @2
    @8
    @0
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @2
    @8
    wb
    #
    @1
    cM
    zre
    cN
    zre
    @9
    @10
    c1
    cr
    wcel
    @11
    1re
    cM
    cN
    c1
    leadd1
    mp3an3
    syl2an
    biimp3a
    3jca
    cM
    cN
    eluz2
    @4
    @6
    eluz2
    3imtr4i
end
