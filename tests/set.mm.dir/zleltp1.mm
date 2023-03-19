include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "1re.mm"
include "leadd1.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "peano2z.mm"
include "zltp1le.mm"
include "sylan2.mm"
include "bitr4d.mm"

theorem zleltp1
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M <_ N <-> M < ( N + 1 ) ) )

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
    cM
    cN
    cle
    wbr
    #
    cM
    c1
    caddc
    co
    cN
    c1
    caddc
    co
    #
    cle
    wbr
    #
    cM
    @3
    clt
    wbr
    #
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
    @4
    wb
    #
    @1
    cM
    zre
    cN
    zre
    @6
    @7
    c1
    cr
    wcel
    @8
    1re
    cM
    cN
    c1
    leadd1
    mp3an3
    syl2an
    @1
    @0
    @3
    cz
    wcel
    @5
    @4
    wb
    cN
    peano2z
    cM
    @3
    zltp1le
    sylan2
    bitr4d
end
