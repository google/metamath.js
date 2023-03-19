include "cltp.mm"
include "cnp.mm"
include "cpp.mm"
include "dmplp.mm"
include "ltrelpr.mm"
include "0npr.mm"
include "wcel.mm"
include "wbr.mm"
include "co.mm"
include "wb.mm"
include "wa.mm"
include "wi.mm"
include "ltaprlem.mm"
include "adantr.mm"
include "wceq.mm"
include "wn.mm"
include "wo.mm"
include "olc.mm"
include "wor.mm"
include "ltsopr.mm"
include "sotric.mm"
include "mpan.mm"
include "adantl.mm"
include "addclpr.mm"
include "anim12dan.mm"
include "sylancr.mm"
include "3imtr3d.mm"
include "con4d.mm"
include "syl5.mm"
include "df-or.mm"
include "syl6ib.mm"
include "com23.mm"
include "soirri.mm"
include "oveq2.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "pm2.21d.mm"
include "pm2.61d2.mm"
include "impbid.mm"
include "3impb.mm"
include "3com13.mm"
include "ndmovord.mm"

theorem ltapr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C e. P. -> ( A <P B <-> ( C +P. A ) <P ( C +P. B ) ) )

  proof
    cA
    cB
    cC
    cltp
    cnp
    cpp
    dmplp
    ltrelpr
    0npr
    cC
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    cA
    cnp
    wcel
    #
    cA
    cB
    cltp
    wbr
    #
    cC
    cA
    cpp
    co
    #
    cC
    cB
    cpp
    co
    #
    cltp
    wbr
    #
    wb
    #
    @0
    @1
    @2
    @7
    @0
    @1
    @2
    wa
    #
    wa
    #
    @3
    @6
    @0
    @3
    @6
    wi
    @8
    cA
    cB
    cC
    ltaprlem
    adantr
    @9
    cB
    cA
    wceq
    #
    @6
    @3
    wi
    @9
    @6
    @10
    wn
    #
    @3
    @9
    @6
    @10
    @3
    wo
    #
    @11
    @3
    wi
    @6
    @5
    @4
    wceq
    #
    @6
    wo
    #
    @9
    @12
    @6
    @13
    olc
    @9
    @12
    @14
    @9
    cB
    cA
    cltp
    wbr
    #
    @5
    @4
    cltp
    wbr
    #
    @12
    wn
    #
    @14
    wn
    #
    @0
    @15
    @16
    wi
    @8
    cB
    cA
    cC
    ltaprlem
    adantr
    @8
    @15
    @17
    wb
    #
    @0
    cnp
    cltp
    wor
    #
    @8
    @19
    ltsopr
    cnp
    cB
    cA
    cltp
    sotric
    mpan
    adantl
    @9
    @20
    @5
    cnp
    wcel
    #
    @4
    cnp
    wcel
    #
    wa
    @16
    @18
    wb
    ltsopr
    @0
    @1
    @21
    @2
    @22
    cC
    cB
    addclpr
    cC
    cA
    addclpr
    anim12dan
    cnp
    @5
    @4
    cltp
    sotric
    sylancr
    3imtr3d
    con4d
    syl5
    @10
    @3
    df-or
    syl6ib
    com23
    @10
    @6
    @3
    @10
    @6
    @4
    @4
    cltp
    wbr
    @4
    cltp
    cnp
    ltsopr
    ltrelpr
    soirri
    @10
    @5
    @4
    @4
    cltp
    cB
    cA
    cC
    cpp
    oveq2
    breq2d
    mtbiri
    pm2.21d
    pm2.61d2
    impbid
    3impb
    3com13
    ndmovord
end
