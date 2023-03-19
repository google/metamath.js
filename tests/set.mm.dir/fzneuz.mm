include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "wceq.mm"
include "wn.mm"
include "c1.mm"
include "caddc.mm"
include "peano2uz.mm"
include "adantl.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "eluzelre.mm"
include "clt.mm"
include "ltp1.mm"
include "wb.mm"
include "peano2re.mm"
include "ltnle.mm"
include "mpdan.mm"
include "mpbid.mm"
include "syl.mm"
include "elfzle2.mm"
include "nsyl.mm"
include "ad2antrr.mm"
include "nelneq2.mm"
include "syl2anc.mm"
include "eqcom.mm"
include "sylnib.mm"
include "eluzfz2.mm"
include "sylancom.mm"
include "pm2.61dan.mm"

theorem fzneuz
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( N e. ( ZZ>= ` M ) /\ K e. ZZ ) -> -. ( M ... N ) = ( ZZ>= ` K ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    cN
    cK
    cuz
    cfv
    #
    wcel
    #
    cM
    cN
    cfz
    co
    #
    @3
    wceq
    #
    wn
    #
    @2
    @4
    wa
    #
    @3
    @5
    wceq
    #
    @6
    @8
    cN
    c1
    caddc
    co
    #
    @3
    wcel
    #
    @10
    @5
    wcel
    #
    wn
    #
    @9
    wn
    @4
    @11
    @2
    cK
    cN
    peano2uz
    adantl
    @0
    @13
    @1
    @4
    @0
    @10
    cN
    cle
    wbr
    #
    @12
    @0
    cN
    cr
    wcel
    #
    @14
    wn
    #
    cM
    cN
    eluzelre
    @15
    cN
    @10
    clt
    wbr
    #
    @16
    cN
    ltp1
    @15
    @10
    cr
    wcel
    @17
    @16
    wb
    cN
    peano2re
    cN
    @10
    ltnle
    mpdan
    mpbid
    syl
    @10
    cM
    cN
    elfzle2
    nsyl
    ad2antrr
    @10
    @3
    @5
    nelneq2
    syl2anc
    @3
    @5
    eqcom
    sylnib
    @2
    @4
    wn
    #
    cN
    @5
    wcel
    #
    @7
    @0
    @19
    @1
    @18
    cM
    cN
    eluzfz2
    ad2antrr
    cN
    @5
    @3
    nelneq2
    sylancom
    pm2.61dan
end
