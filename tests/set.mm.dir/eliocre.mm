include "cr.mm"
include "wcel.mm"
include "cioc.mm"
include "co.mm"
include "wa.mm"
include "cxr.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "df-ioc.mm"
include "elixx3g.mm"
include "biimpi.mm"
include "simpld.mm"
include "simp3d.mm"
include "adantl.mm"
include "simpl.mm"
include "mnfxr.mm"
include "a1i.mm"
include "simp1d.mm"
include "mnfle.mm"
include "syl.mm"
include "simprd.mm"
include "xrlelttrd.mm"
include "xrre.mm"
include "syl22anc.mm"

theorem eliocre
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( B e. RR /\ C e. ( A (,] B ) ) -> C e. RR )

  proof
    cB
    cr
    wcel
    #
    cC
    cA
    cB
    cioc
    co
    wcel
    #
    wa
    cC
    cxr
    wcel
    #
    @0
    cmnf
    cC
    clt
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    cC
    cr
    wcel
    @1
    @2
    @0
    @1
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @2
    @1
    @5
    @6
    @2
    w3a
    #
    cA
    cC
    clt
    wbr
    #
    @4
    wa
    #
    @1
    @7
    @9
    wa
    vx
    vy
    vz
    cA
    cB
    cC
    clt
    cle
    cioc
    vx
    vy
    vz
    df-ioc
    elixx3g
    biimpi
    #
    simpld
    #
    simp3d
    #
    adantl
    @0
    @1
    simpl
    @1
    @3
    @0
    @1
    cmnf
    cA
    cC
    cmnf
    cxr
    wcel
    @1
    mnfxr
    a1i
    @1
    @5
    @6
    @2
    @11
    simp1d
    #
    @12
    @1
    @5
    cmnf
    cA
    cle
    wbr
    @13
    cA
    mnfle
    syl
    @1
    @8
    @4
    @1
    @7
    @9
    @10
    simprd
    #
    simpld
    xrlelttrd
    adantl
    @1
    @4
    @0
    @1
    @8
    @4
    @14
    simprd
    adantl
    cC
    cB
    xrre
    syl22anc
end
