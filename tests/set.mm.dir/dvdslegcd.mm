include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "cdvds.mm"
include "wbr.mm"
include "cgcd.mm"
include "co.mm"
include "cle.mm"
include "wi.mm"
include "cv.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cn.mm"
include "cpr.mm"
include "wral.mm"
include "eqid.mm"
include "gcdcllem3.mm"
include "simp3d.mm"
include "gcdn0val.mm"
include "breq2d.mm"
include "sylibrd.mm"
include "com12.mm"
include "3expb.mm"
include "exp4b.mm"
include "com23.mm"
include "impcom.mm"
include "3impb.mm"
include "imp.mm"

theorem dvdslegcd
  let cK: class K
  let cM: class M
  let cN: class N
  let vn: setvar n
  let vz: setvar z


  assert |- ( ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) /\ -. ( M = 0 /\ N = 0 ) ) -> ( ( K || M /\ K || N ) -> K <_ ( M gcd N ) ) )

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
    cM
    cc0
    wceq
    cN
    cc0
    wceq
    wa
    wn
    #
    cK
    cM
    cdvds
    wbr
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
    cgcd
    co
    #
    cle
    wbr
    #
    wi
    #
    @0
    @1
    @2
    @3
    @9
    wi
    #
    @1
    @2
    wa
    #
    @0
    @10
    @11
    @3
    @0
    @9
    @11
    @3
    @0
    @6
    @8
    @0
    @6
    wa
    @11
    @3
    wa
    #
    @8
    @0
    @4
    @5
    @12
    @8
    wi
    @12
    @0
    @4
    @5
    w3a
    #
    @8
    @12
    @13
    cK
    vn
    cv
    #
    cM
    cdvds
    wbr
    @14
    cN
    cdvds
    wbr
    wa
    vn
    cz
    crab
    #
    cr
    clt
    csup
    #
    cle
    wbr
    #
    @8
    @12
    @16
    cn
    wcel
    @16
    cM
    cdvds
    wbr
    @16
    cN
    cdvds
    wbr
    wa
    @13
    @17
    wi
    vn
    @15
    @14
    vz
    cv
    cdvds
    wbr
    vz
    cM
    cN
    cpr
    wral
    vn
    cz
    crab
    #
    vz
    cK
    cM
    cN
    @18
    eqid
    @15
    eqid
    gcdcllem3
    simp3d
    @12
    @7
    @16
    cK
    cle
    vn
    cM
    cN
    gcdn0val
    breq2d
    sylibrd
    com12
    3expb
    com12
    exp4b
    com23
    impcom
    3impb
    imp
end
