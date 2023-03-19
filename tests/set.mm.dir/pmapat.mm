include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "csn.mm"
include "cbs.mm"
include "eqid.mm"
include "atbase.mm"
include "pmapval.mm"
include "sylan2.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simplr.mm"
include "atcmp.mm"
include "syl3anc.mm"
include "rabbidva.mm"
include "rabsn.mm"
include "adantl.mm"
include "3eqtrd.mm"

theorem pmapat
  let cA: class A
  let cP: class P
  let cK: class K
  let cM: class M
  let vq: setvar q
  assume pmapat.a: |- A = ( Atoms ` K )
  assume pmapat.m: |- M = ( pmap ` K )


  assert |- ( ( K e. HL /\ P e. A ) -> ( M ` P ) = { P } )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    wa
    #
    cP
    cM
    cfv
    #
    vq
    cv
    #
    cP
    cK
    cple
    cfv
    #
    wbr
    #
    vq
    cA
    crab
    #
    @4
    cP
    wceq
    #
    vq
    cA
    crab
    #
    cP
    csn
    #
    @1
    @0
    cP
    cK
    cbs
    cfv
    #
    wcel
    @3
    @7
    wceq
    cA
    @11
    cP
    cK
    @11
    eqid
    #
    pmapat.a
    atbase
    cA
    @11
    chlt
    cK
    @5
    cM
    cP
    vq
    @12
    @5
    eqid
    #
    pmapat.a
    pmapat.m
    pmapval
    sylan2
    @2
    @6
    @8
    vq
    cA
    @2
    @4
    cA
    wcel
    #
    wa
    cK
    cal
    wcel
    #
    @14
    @1
    @6
    @8
    wb
    @0
    @15
    @1
    @14
    cK
    hlatl
    ad2antrr
    @2
    @14
    simpr
    @0
    @1
    @14
    simplr
    cA
    @4
    cP
    cK
    @5
    @13
    pmapat.a
    atcmp
    syl3anc
    rabbidva
    @1
    @9
    @10
    wceq
    @0
    vq
    cA
    cP
    rabsn
    adantl
    3eqtrd
end
