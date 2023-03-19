include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "wceq.mm"
include "wa.mm"
include "zre.mm"
include "leidd.mm"
include "adantr.mm"
include "breq1.mm"
include "bibi12d.mm"
include "rspcva.mm"
include "mpbid.mm"
include "adantlr.mm"
include "mpbird.mm"
include "adantll.mm"
include "jca.mm"
include "ex.mm"
include "cr.mm"
include "letri3.mm"
include "syl2an.mm"
include "sylibrd.mm"
include "3impia.mm"

theorem zextle
  let vk: setvar k
  let cM: class M
  let cN: class N

  disjoint M k
  disjoint N k
  assert |- ( ( M e. ZZ /\ N e. ZZ /\ A. k e. ZZ ( k <_ M <-> k <_ N ) ) -> M = N )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    vk
    cv
    #
    cM
    cle
    wbr
    #
    @2
    cN
    cle
    wbr
    #
    wb
    #
    vk
    cz
    wral
    #
    cM
    cN
    wceq
    #
    @0
    @1
    wa
    #
    @6
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cle
    wbr
    #
    wa
    #
    @7
    @8
    @6
    @11
    @8
    @6
    wa
    @9
    @10
    @0
    @6
    @9
    @1
    @0
    @6
    wa
    cM
    cM
    cle
    wbr
    #
    @9
    @0
    @12
    @6
    @0
    cM
    cM
    zre
    #
    leidd
    adantr
    @5
    @12
    @9
    wb
    vk
    cM
    cz
    @2
    cM
    wceq
    @3
    @12
    @4
    @9
    @2
    cM
    cM
    cle
    breq1
    @2
    cM
    cN
    cle
    breq1
    bibi12d
    rspcva
    mpbid
    adantlr
    @1
    @6
    @10
    @0
    @1
    @6
    wa
    @10
    cN
    cN
    cle
    wbr
    #
    @1
    @14
    @6
    @1
    cN
    cN
    zre
    #
    leidd
    adantr
    @5
    @10
    @14
    wb
    vk
    cN
    cz
    @2
    cN
    wceq
    @3
    @10
    @4
    @14
    @2
    cN
    cM
    cle
    breq1
    @2
    cN
    cN
    cle
    breq1
    bibi12d
    rspcva
    mpbird
    adantll
    jca
    ex
    @0
    cM
    cr
    wcel
    cN
    cr
    wcel
    @7
    @11
    wb
    @1
    @13
    @15
    cM
    cN
    letri3
    syl2an
    sylibrd
    3impia
end
