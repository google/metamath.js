include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "cmnf.mm"
include "cpnf.mm"
include "wi.mm"
include "cle.mm"
include "mnfle.mm"
include "adantr.mm"
include "mnfxr.mm"
include "xrlelttr.mm"
include "mp3an1.mm"
include "mpand.mm"
include "3adant3.mm"
include "pnfge.mm"
include "adantl.mm"
include "pnfxr.mm"
include "xrltletr.mm"
include "mp3an3.mm"
include "mpan2d.mm"
include "3adant1.mm"
include "anim12d.mm"
include "wb.mm"
include "xrrebnd.mm"
include "3ad2ant2.mm"
include "sylibrd.mm"
include "imp.mm"

theorem xrre2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ ( A < B /\ B < C ) ) -> B e. RR )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cC
    clt
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    @3
    @6
    cmnf
    cB
    clt
    wbr
    #
    cB
    cpnf
    clt
    wbr
    #
    wa
    #
    @7
    @3
    @4
    @8
    @5
    @9
    @0
    @1
    @4
    @8
    wi
    @2
    @0
    @1
    wa
    cmnf
    cA
    cle
    wbr
    #
    @4
    @8
    @0
    @11
    @1
    cA
    mnfle
    adantr
    cmnf
    cxr
    wcel
    @0
    @1
    @11
    @4
    wa
    @8
    wi
    mnfxr
    cmnf
    cA
    cB
    xrlelttr
    mp3an1
    mpand
    3adant3
    @1
    @2
    @5
    @9
    wi
    @0
    @1
    @2
    wa
    @5
    cC
    cpnf
    cle
    wbr
    #
    @9
    @2
    @12
    @1
    cC
    pnfge
    adantl
    @1
    @2
    cpnf
    cxr
    wcel
    @5
    @12
    wa
    @9
    wi
    pnfxr
    cB
    cC
    cpnf
    xrltletr
    mp3an3
    mpan2d
    3adant1
    anim12d
    @1
    @0
    @7
    @10
    wb
    @2
    cB
    xrrebnd
    3ad2ant2
    sylibrd
    imp
end
