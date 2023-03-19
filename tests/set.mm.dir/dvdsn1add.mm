include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "simp1.mm"
include "zaddcl.mm"
include "3adant1.mm"
include "simp3.mm"
include "3jca.mm"
include "ad2antrr.mm"
include "pm3.22.mm"
include "adantll.mm"
include "dvds2sub.mm"
include "sylc.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "zcnd.mm"
include "pncand.mm"
include "breqtrd.mm"
include "adantlrl.mm"
include "simplrl.mm"
include "pm2.65da.mm"
include "ex.mm"

theorem dvdsn1add
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( -. K || M /\ K || N ) -> -. K || ( M + N ) ) )

  proof
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cK
    cM
    cdvds
    wbr
    #
    wn
    #
    cK
    cN
    cdvds
    wbr
    #
    wa
    #
    cK
    cM
    cN
    caddc
    co
    #
    cdvds
    wbr
    #
    wn
    @3
    @7
    wa
    @9
    @4
    @3
    @6
    @9
    @4
    @5
    @3
    @6
    wa
    @9
    wa
    #
    cK
    @8
    cN
    cmin
    co
    #
    cM
    cdvds
    @10
    @0
    @8
    cz
    wcel
    #
    @2
    w3a
    #
    @9
    @6
    wa
    #
    cK
    @11
    cdvds
    wbr
    @3
    @13
    @6
    @9
    @3
    @0
    @12
    @2
    @0
    @1
    @2
    simp1
    @1
    @2
    @12
    @0
    cM
    cN
    zaddcl
    3adant1
    @0
    @1
    @2
    simp3
    #
    3jca
    ad2antrr
    @6
    @9
    @14
    @3
    @6
    @9
    pm3.22
    adantll
    cK
    @8
    cN
    dvds2sub
    sylc
    @10
    cM
    cN
    @3
    cM
    cc
    wcel
    #
    @6
    @9
    @1
    @0
    @16
    @2
    cM
    zcn
    3ad2ant2
    ad2antrr
    @3
    cN
    cc
    wcel
    @6
    @9
    @3
    cN
    @15
    zcnd
    ad2antrr
    pncand
    breqtrd
    adantlrl
    @3
    @5
    @6
    @9
    simplrl
    pm2.65da
    ex
end
