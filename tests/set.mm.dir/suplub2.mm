include "wcel.mm"
include "wa.mm"
include "csup.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "suplub.mm"
include "expdimp.mm"
include "breq2.mm"
include "cbvrexv.mm"
include "wceq.mm"
include "wi.mm"
include "biimprd.mm"
include "a1i.mm"
include "wor.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "wss.mm"
include "adantr.mm"
include "sselda.mm"
include "supcl.mm"
include "sotr.mm"
include "syl13anc.mm"
include "expcomd.mm"
include "wo.mm"
include "wn.mm"
include "supub.mm"
include "imp.mm"
include "wb.mm"
include "sotric.mm"
include "syl12anc.mm"
include "con2bid.mm"
include "mpbird.mm"
include "mpjaod.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "impbid.mm"

theorem suplub2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vw: setvar w
  assume supmo.1: |- ( ph -> R Or A )
  assume supcl.2: |- ( ph -> E. x e. A ( A. y e. B -. x R y /\ A. y e. A ( y R x -> E. z e. B y R z ) ) )
  assume suplub2.3: |- ( ph -> B C_ A )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint R w
  disjoint B w
  disjoint C w
  disjoint ph w
  assert |- ( ( ph /\ C e. A ) -> ( C R sup ( B , A , R ) <-> E. z e. B C R z ) )

  proof
    wph
    cC
    cA
    wcel
    #
    wa
    #
    cC
    cB
    cA
    cR
    csup
    #
    cR
    wbr
    #
    cC
    vz
    cv
    #
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    wph
    @0
    @3
    @6
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cR
    supmo.1
    supcl.2
    suplub
    expdimp
    @6
    cC
    vw
    cv
    #
    cR
    wbr
    #
    vw
    cB
    wrex
    @1
    @3
    @5
    @8
    vz
    vw
    cB
    @4
    @7
    cC
    cR
    breq2
    cbvrexv
    @1
    @8
    @3
    vw
    cB
    @1
    @7
    cB
    wcel
    #
    wa
    #
    @2
    @7
    wceq
    #
    @8
    @3
    wi
    #
    @7
    @2
    cR
    wbr
    #
    @11
    @12
    wi
    @10
    @11
    @3
    @8
    @2
    @7
    cC
    cR
    breq2
    biimprd
    a1i
    @10
    @8
    @13
    @3
    @10
    cA
    cR
    wor
    #
    @0
    @7
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    @8
    @13
    wa
    @3
    wi
    wph
    @14
    @0
    @9
    supmo.1
    ad2antrr
    #
    wph
    @0
    @9
    simplr
    @1
    cB
    cA
    @7
    wph
    cB
    cA
    wss
    @0
    suplub2.3
    adantr
    sselda
    #
    wph
    @16
    @0
    @9
    wph
    vx
    vy
    vz
    cA
    cB
    cR
    supmo.1
    supcl.2
    supcl
    ad2antrr
    #
    cA
    cC
    @7
    @2
    cR
    sotr
    syl13anc
    expcomd
    @10
    @11
    @13
    wo
    #
    @2
    @7
    cR
    wbr
    #
    wn
    #
    @1
    @9
    @22
    wph
    @9
    @22
    wi
    @0
    wph
    vx
    vy
    vz
    cA
    cB
    @7
    cR
    supmo.1
    supcl.2
    supub
    adantr
    imp
    @10
    @21
    @20
    @10
    @14
    @16
    @15
    @21
    @20
    wn
    wb
    @17
    @19
    @18
    cA
    @2
    @7
    cR
    sotric
    syl12anc
    con2bid
    mpbird
    mpjaod
    rexlimdva
    syl5bi
    impbid
end
