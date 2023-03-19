include "cr.mm"
include "wcel.mm"
include "cico.mm"
include "co.mm"
include "wa.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "clt.mm"
include "w3a.mm"
include "df-ico.mm"
include "elixx3g.mm"
include "biimpi.mm"
include "simpld.mm"
include "simp3d.mm"
include "adantl.mm"
include "simpl.mm"
include "simprd.mm"
include "simp2d.mm"
include "pnfxr.mm"
include "a1i.mm"
include "pnfge.mm"
include "syl.mm"
include "xrltletrd.mm"
include "xrre3.mm"
include "syl22anc.mm"

theorem elicore
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR /\ C e. ( A [,) B ) ) -> C e. RR )

  proof
    cA
    cr
    wcel
    #
    cC
    cA
    cB
    cico
    co
    wcel
    #
    wa
    #
    cC
    cxr
    wcel
    #
    @0
    cA
    cC
    cle
    wbr
    #
    cC
    cpnf
    clt
    wbr
    cC
    cr
    wcel
    @1
    @3
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
    @3
    @1
    @5
    @6
    @3
    w3a
    #
    @4
    cC
    cB
    clt
    wbr
    #
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
    cle
    clt
    cico
    vx
    vy
    vz
    df-ico
    elixx3g
    biimpi
    #
    simpld
    #
    simp3d
    adantl
    #
    @0
    @1
    simpl
    @1
    @4
    @0
    @1
    @4
    @8
    @1
    @7
    @9
    @10
    simprd
    #
    simpld
    adantl
    @2
    cC
    cB
    cpnf
    @12
    @1
    @6
    @0
    @1
    @5
    @6
    @3
    @11
    simp2d
    #
    adantl
    cpnf
    cxr
    wcel
    @2
    pnfxr
    a1i
    @1
    @8
    @0
    @1
    @4
    @8
    @13
    simprd
    adantl
    @1
    cB
    cpnf
    cle
    wbr
    #
    @0
    @1
    @6
    @15
    @14
    cB
    pnfge
    syl
    adantl
    xrltletrd
    cC
    cA
    xrre3
    syl22anc
end
