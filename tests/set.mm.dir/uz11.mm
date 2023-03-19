include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "uzid.mm"
include "eleq2.mm"
include "eluzel2.mm"
include "syl6bi.mm"
include "mpan9.mm"
include "cle.mm"
include "wbr.mm"
include "syl5ibr.mm"
include "eluzle.mm"
include "syl6.mm"
include "syl5ib.mm"
include "anim12d.mm"
include "impl.mm"
include "ancoms.mm"
include "anassrs.mm"
include "wb.mm"
include "cr.mm"
include "zre.mm"
include "letri3.mm"
include "syl2an.mm"
include "adantlr.mm"
include "mpbird.mm"
include "mpdan.mm"
include "ex.mm"
include "fveq2.mm"
include "impbid1.mm"

theorem uz11
  let cM: class M
  let cN: class N


  assert |- ( M e. ZZ -> ( ( ZZ>= ` M ) = ( ZZ>= ` N ) <-> M = N ) )

  proof
    cM
    cz
    wcel
    #
    cM
    cuz
    cfv
    #
    cN
    cuz
    cfv
    #
    wceq
    #
    cM
    cN
    wceq
    #
    @0
    @3
    @4
    @0
    @3
    wa
    #
    cN
    cz
    wcel
    #
    @4
    @0
    cM
    @1
    wcel
    #
    @3
    @6
    cM
    uzid
    #
    @3
    @7
    cM
    @2
    wcel
    #
    @6
    @1
    @2
    cM
    eleq2
    #
    cN
    cM
    eluzel2
    syl6bi
    mpan9
    @5
    @6
    wa
    @4
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
    @0
    @3
    @6
    @13
    @3
    @6
    wa
    @0
    @13
    @3
    @6
    @0
    @13
    @3
    @6
    @11
    @0
    @12
    @3
    @6
    cN
    @1
    wcel
    #
    @11
    @6
    @14
    @3
    cN
    @2
    wcel
    cN
    uzid
    @1
    @2
    cN
    eleq2
    syl5ibr
    cM
    cN
    eluzle
    syl6
    @3
    @0
    @9
    @12
    @0
    @7
    @3
    @9
    @8
    @10
    syl5ib
    cN
    cM
    eluzle
    syl6
    anim12d
    impl
    ancoms
    anassrs
    @0
    @6
    @4
    @13
    wb
    #
    @3
    @0
    cM
    cr
    wcel
    cN
    cr
    wcel
    @15
    @6
    cM
    zre
    cN
    zre
    cM
    cN
    letri3
    syl2an
    adantlr
    mpbird
    mpdan
    ex
    cM
    cN
    cuz
    fveq2
    impbid1
end
