include "cxr.mm"
include "wss.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cun.mm"
include "wcel.mm"
include "cv.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cr.mm"
include "wceq.mm"
include "wa.mm"
include "unss.mm"
include "biimpi.mm"
include "3adant3.mm"
include "supxrcl.mm"
include "3ad2ant2.mm"
include "wo.mm"
include "elun.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "xrsupss.mm"
include "supub.mm"
include "3ad2ant1.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "ssel2.mm"
include "adantlr.mm"
include "xrlelttr.mm"
include "syl3anc.mm"
include "expdimp.mm"
include "con3d.mm"
include "exp41.mm"
include "com34.mm"
include "3imp.mm"
include "mpdd.mm"
include "jaod.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "rexr.mm"
include "suplub.mm"
include "sylani.mm"
include "elun2.mm"
include "anim1i.mm"
include "reximi2.mm"
include "syl6.mm"
include "expd.mm"
include "supxr.mm"
include "syl22anc.mm"

theorem supxrun
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( A C_ RR* /\ B C_ RR* /\ sup ( A , RR* , < ) <_ sup ( B , RR* , < ) ) -> sup ( ( A u. B ) , RR* , < ) = sup ( B , RR* , < ) )

  proof
    cA
    cxr
    wss
    #
    cB
    cxr
    wss
    #
    cA
    cxr
    clt
    csup
    #
    cB
    cxr
    clt
    csup
    #
    cle
    wbr
    #
    w3a
    #
    cA
    cB
    cun
    #
    cxr
    wss
    #
    @3
    cxr
    wcel
    #
    @3
    vx
    cv
    #
    clt
    wbr
    #
    wn
    #
    vx
    @6
    wral
    @9
    @3
    clt
    wbr
    #
    @9
    vy
    cv
    #
    clt
    wbr
    #
    vy
    @6
    wrex
    #
    wi
    #
    vx
    cr
    wral
    #
    @6
    cxr
    clt
    csup
    @3
    wceq
    @0
    @1
    @7
    @4
    @0
    @1
    wa
    #
    @7
    cA
    cB
    cxr
    unss
    biimpi
    3adant3
    @1
    @0
    @8
    @4
    cB
    supxrcl
    #
    3ad2ant2
    @5
    @11
    vx
    @6
    @9
    @6
    wcel
    @9
    cA
    wcel
    #
    @9
    cB
    wcel
    #
    wo
    @5
    @11
    @9
    cA
    cB
    elun
    @5
    @20
    @11
    @21
    @5
    @20
    @2
    @9
    clt
    wbr
    #
    wn
    #
    @11
    @0
    @1
    @20
    @23
    wi
    @4
    @0
    vy
    vz
    vw
    cxr
    cA
    @9
    clt
    cxr
    clt
    wor
    #
    @0
    xrltso
    a1i
    vy
    vz
    vw
    cA
    xrsupss
    supub
    3ad2ant1
    @0
    @1
    @4
    @20
    @23
    @11
    wi
    #
    wi
    @0
    @1
    @20
    @4
    @25
    @0
    @1
    @20
    @4
    @25
    @18
    @20
    wa
    #
    @4
    wa
    @10
    @22
    @26
    @4
    @10
    @22
    @26
    @2
    cxr
    wcel
    #
    @8
    @9
    cxr
    wcel
    #
    @4
    @10
    wa
    @22
    wi
    @0
    @27
    @1
    @20
    cA
    supxrcl
    ad2antrr
    @1
    @8
    @0
    @20
    @19
    ad2antlr
    @0
    @20
    @28
    @1
    cA
    cxr
    @9
    ssel2
    adantlr
    @2
    @3
    @9
    xrlelttr
    syl3anc
    expdimp
    con3d
    exp41
    com34
    3imp
    mpdd
    @1
    @0
    @21
    @11
    wi
    @4
    @1
    vy
    vz
    vw
    cxr
    cB
    @9
    clt
    @24
    @1
    xrltso
    a1i
    #
    vy
    vz
    vw
    cB
    xrsupss
    supub
    3ad2ant2
    jaod
    syl5bi
    ralrimiv
    @1
    @0
    @17
    @4
    @1
    @16
    vx
    cr
    @1
    @9
    cr
    wcel
    #
    @12
    @15
    @1
    @30
    @12
    wa
    @14
    vy
    cB
    wrex
    #
    @15
    @30
    @1
    @28
    @12
    @31
    @9
    rexr
    @1
    vx
    vz
    vy
    cxr
    cB
    @9
    clt
    @29
    vx
    vz
    vy
    cB
    xrsupss
    suplub
    sylani
    @14
    @14
    vy
    cB
    @6
    @13
    cB
    wcel
    @13
    @6
    wcel
    @14
    @13
    cB
    cA
    elun2
    anim1i
    reximi2
    syl6
    expd
    ralrimiv
    3ad2ant2
    vx
    vy
    @6
    @3
    supxr
    syl22anc
end
