include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "wo.mm"
include "elfzo2.mm"
include "cle.mm"
include "wi.mm"
include "eluz2.mm"
include "wa.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "leloe.mm"
include "syl2an.mm"
include "peano2z.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "simprlr.mm"
include "simpl.mm"
include "zltp1le.mm"
include "mpbid.mm"
include "3jca.mm"
include "simplrr.mm"
include "simpr.mm"
include "3anbi1i.mm"
include "bitri.mm"
include "syl3anbrc.mm"
include "olcd.mm"
include "exp31.mm"
include "orc.mm"
include "eqcoms.mm"
include "2a1d.mm"
include "jaoi.mm"
include "expd.mm"
include "com12.mm"
include "sylbid.mm"
include "3impia.mm"
include "sylbi.mm"
include "3imp.mm"

theorem elfzolborelfzop1
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( K e. ( M ..^ N ) -> ( K = M \/ K e. ( ( M + 1 ) ..^ N ) ) )

  proof
    cK
    cM
    cN
    cfzo
    co
    wcel
    cK
    cM
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cN
    clt
    wbr
    #
    w3a
    cK
    cM
    wceq
    #
    cK
    cM
    c1
    caddc
    co
    #
    cN
    cfzo
    co
    wcel
    #
    wo
    #
    cK
    cM
    cN
    elfzo2
    @0
    @1
    @2
    @6
    @0
    cM
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    cM
    cK
    cle
    wbr
    #
    w3a
    @1
    @2
    @6
    wi
    #
    wi
    #
    cM
    cK
    eluz2
    @7
    @8
    @9
    @11
    @7
    @8
    wa
    #
    @9
    cM
    cK
    clt
    wbr
    #
    cM
    cK
    wceq
    #
    wo
    #
    @11
    @7
    cM
    cr
    wcel
    cK
    cr
    wcel
    @9
    @15
    wb
    @8
    cM
    zre
    cK
    zre
    cM
    cK
    leloe
    syl2an
    @15
    @12
    @11
    @15
    @12
    @1
    @10
    @13
    @12
    @1
    wa
    #
    @10
    wi
    @14
    @13
    @16
    @2
    @6
    @13
    @16
    wa
    #
    @2
    wa
    #
    @5
    @3
    @18
    @4
    cz
    wcel
    #
    @8
    @4
    cK
    cle
    wbr
    #
    w3a
    #
    @1
    @2
    @5
    @17
    @21
    @2
    @17
    @19
    @8
    @20
    @12
    @19
    @13
    @1
    @7
    @19
    @8
    cM
    peano2z
    adantr
    ad2antrl
    @13
    @7
    @8
    @1
    simprlr
    @17
    @13
    @20
    @13
    @16
    simpl
    @12
    @13
    @20
    wb
    @13
    @1
    cM
    cK
    zltp1le
    ad2antrl
    mpbid
    3jca
    adantr
    @13
    @12
    @1
    @2
    simplrr
    @17
    @2
    simpr
    @5
    cK
    @4
    cuz
    cfv
    wcel
    #
    @1
    @2
    w3a
    @21
    @1
    @2
    w3a
    cK
    @4
    cN
    elfzo2
    @22
    @21
    @1
    @2
    @4
    cK
    eluz2
    3anbi1i
    bitri
    syl3anbrc
    olcd
    exp31
    @14
    @6
    @16
    @2
    @6
    cK
    cM
    @3
    @5
    orc
    eqcoms
    2a1d
    jaoi
    expd
    com12
    sylbid
    3impia
    sylbi
    3imp
    sylbi
end
