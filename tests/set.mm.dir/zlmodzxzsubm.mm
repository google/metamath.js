include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "cpr.mm"
include "co.mm"
include "zring.mm"
include "cminusg.mm"
include "cfv.mm"
include "cvsca.mm"
include "cplusg.mm"
include "cneg.mm"
include "clmod.mm"
include "cbs.mm"
include "wceq.mm"
include "csca.mm"
include "zlmodzxzlmod.mm"
include "simpli.mm"
include "a1i.mm"
include "zlmodzxzel.mm"
include "ad2ant2r.mm"
include "ad2ant2l.mm"
include "eqid.mm"
include "simpri.mm"
include "zring1.mm"
include "lmodvsubval2.mm"
include "syl3anc.mm"
include "1z.mm"
include "zringinvg.mm"
include "mp1i.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem zlmodzxzsubm
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.mi: class .-
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k
  assume zlmodzxz.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzsub.m: |- .- = ( -g ` Z )


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) ) -> ( { <. 0 , A >. , <. 1 , C >. } .- { <. 0 , B >. , <. 1 , D >. } ) = ( { <. 0 , A >. , <. 1 , C >. } ( +g ` Z ) ( -u 1 ( .s ` Z ) { <. 0 , B >. , <. 1 , D >. } ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    cC
    cz
    wcel
    #
    cD
    cz
    wcel
    #
    wa
    wa
    #
    cc0
    cA
    cop
    c1
    cC
    cop
    cpr
    #
    cc0
    cB
    cop
    c1
    cD
    cop
    cpr
    #
    c.mi
    co
    #
    @5
    c1
    zring
    cminusg
    cfv
    #
    cfv
    #
    @6
    cZ
    cvsca
    cfv
    #
    co
    #
    cZ
    cplusg
    cfv
    #
    co
    #
    @5
    c1
    cneg
    #
    @6
    @10
    co
    #
    @12
    co
    @4
    cZ
    clmod
    wcel
    #
    @5
    cZ
    cbs
    cfv
    #
    wcel
    #
    @6
    @17
    wcel
    #
    @7
    @13
    wceq
    @16
    @4
    @16
    zring
    cZ
    csca
    cfv
    wceq
    #
    cZ
    zlmodzxz.z
    zlmodzxzlmod
    #
    simpli
    a1i
    @0
    @2
    @18
    @1
    @3
    cA
    cC
    cZ
    zlmodzxz.z
    zlmodzxzel
    ad2ant2r
    @1
    @3
    @19
    @0
    @2
    cB
    cD
    cZ
    zlmodzxz.z
    zlmodzxzel
    ad2ant2l
    @5
    @6
    @12
    @10
    c1
    zring
    c.mi
    @8
    @17
    cZ
    @17
    eqid
    @12
    eqid
    zlmodzxzsub.m
    @16
    @20
    @21
    simpri
    @10
    eqid
    @8
    eqid
    zring1
    lmodvsubval2
    syl3anc
    @4
    @11
    @15
    @5
    @12
    @4
    @9
    @14
    @6
    @10
    @4
    @14
    @9
    c1
    cz
    wcel
    @14
    @9
    wceq
    @4
    1z
    c1
    zringinvg
    mp1i
    eqcomd
    oveq1d
    oveq2d
    eqtrd
end
