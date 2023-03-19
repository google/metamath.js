include "cref.mm"
include "wbr.mm"
include "wa.mm"
include "cuni.mm"
include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "eqid.mm"
include "refbas.mm"
include "sylan9eqr.mm"
include "wcel.mm"
include "wi.mm"
include "refssex.mm"
include "ex.mm"
include "adantr.mm"
include "ad2ant2lr.mm"
include "sstr2.mm"
include "reximdv.mm"
include "ad2antll.mm"
include "mpd.mm"
include "rexlimdvaa.mm"
include "syld.mm"
include "ralrimiv.mm"
include "cvv.mm"
include "wb.mm"
include "refrel.mm"
include "brrelexi.mm"
include "isref.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem reftr
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A Ref B /\ B Ref C ) -> A Ref C )

  proof
    cA
    cB
    cref
    wbr
    #
    cB
    cC
    cref
    wbr
    #
    wa
    #
    cA
    cC
    cref
    wbr
    #
    cC
    cuni
    #
    cA
    cuni
    #
    wceq
    #
    vx
    cv
    #
    vz
    cv
    #
    wss
    #
    vz
    cC
    wrex
    #
    vx
    cA
    wral
    #
    @1
    @0
    @4
    cB
    cuni
    #
    @5
    cB
    cC
    @12
    @4
    @12
    eqid
    #
    @4
    eqid
    #
    refbas
    cA
    cB
    @5
    @12
    @5
    eqid
    #
    @13
    refbas
    sylan9eqr
    @2
    @10
    vx
    cA
    @2
    @7
    cA
    wcel
    #
    @7
    vy
    cv
    #
    wss
    #
    vy
    cB
    wrex
    #
    @10
    @0
    @16
    @19
    wi
    @1
    @0
    @16
    @19
    vy
    cA
    cB
    @7
    refssex
    ex
    adantr
    @2
    @18
    @10
    vy
    cB
    @2
    @17
    cB
    wcel
    #
    @18
    wa
    wa
    @17
    @8
    wss
    #
    vz
    cC
    wrex
    #
    @10
    @1
    @20
    @22
    @0
    @18
    vz
    cB
    cC
    @17
    refssex
    ad2ant2lr
    @18
    @22
    @10
    wi
    @2
    @20
    @18
    @21
    @9
    vz
    cC
    @7
    @17
    @8
    sstr2
    reximdv
    ad2antll
    mpd
    rexlimdvaa
    syld
    ralrimiv
    @2
    cA
    cvv
    wcel
    #
    @3
    @6
    @11
    wa
    wb
    @0
    @23
    @1
    cA
    cB
    cref
    refrel
    brrelexi
    adantr
    vx
    vz
    cA
    cC
    cvv
    @5
    @4
    @15
    @14
    isref
    syl
    mpbir2and
end
