include "cnlly.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "wrex.mm"
include "cpw.mm"
include "nllyi.mm"
include "simprrl.mm"
include "selpw.mm"
include "sylibr.mm"
include "ctop.mm"
include "simpl1.mm"
include "nllytop.mm"
include "syl.mm"
include "simprl.mm"
include "neii2.mm"
include "syl2anc.mm"
include "wb.mm"
include "simpll3.mm"
include "snssg.mm"
include "mpbird.mm"
include "simprr.mm"
include "simprrr.mm"
include "adantr.mm"
include "3jca.mm"
include "ex.mm"
include "reximdv.mm"
include "mpd.mm"
include "jca.mm"
include "reximdv2.mm"

theorem nlly2i
  let vu: setvar u
  let cA: class A
  let cP: class P
  let cU: class U
  let cJ: class J
  let vs: setvar s
  let vj: setvar j
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cV: class V

  disjoint s u
  disjoint A s
  disjoint A u
  disjoint P s
  disjoint P u
  disjoint U s
  disjoint U u
  disjoint J s
  disjoint J u
  disjoint j s
  disjoint j u
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B j
  disjoint B u
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P y
  disjoint U x
  disjoint U y
  disjoint J j
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint V u
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( ( J e. N-Locally A /\ U e. J /\ P e. U ) -> E. s e. ~P U E. u e. J ( P e. u /\ u C_ s /\ ( J |`t s ) e. A ) )

  proof
    cJ
    cA
    cnlly
    wcel
    #
    cU
    cJ
    wcel
    #
    cP
    cU
    wcel
    #
    w3a
    #
    vs
    cv
    #
    cU
    wss
    #
    cJ
    @4
    crest
    co
    cA
    wcel
    #
    wa
    #
    vs
    cP
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    wrex
    cP
    vu
    cv
    #
    wcel
    #
    @10
    @4
    wss
    #
    @6
    w3a
    #
    vu
    cJ
    wrex
    #
    vs
    cU
    cpw
    #
    wrex
    vs
    cA
    cP
    cU
    cJ
    nllyi
    @3
    @7
    @14
    vs
    @9
    @15
    @3
    @4
    @9
    wcel
    #
    @7
    wa
    #
    @4
    @15
    wcel
    #
    @14
    wa
    @3
    @17
    wa
    #
    @18
    @14
    @19
    @5
    @18
    @3
    @16
    @5
    @6
    simprrl
    vs
    cU
    selpw
    sylibr
    @19
    @8
    @10
    wss
    #
    @12
    wa
    #
    vu
    cJ
    wrex
    #
    @14
    @19
    cJ
    ctop
    wcel
    #
    @16
    @22
    @19
    @0
    @23
    @0
    @1
    @2
    @17
    simpl1
    cA
    cJ
    nllytop
    syl
    @3
    @16
    @7
    simprl
    @8
    vu
    cJ
    @4
    neii2
    syl2anc
    @19
    @21
    @13
    vu
    cJ
    @19
    @21
    @13
    @19
    @21
    wa
    #
    @11
    @12
    @6
    @24
    @11
    @20
    @19
    @20
    @12
    simprl
    @24
    @2
    @11
    @20
    wb
    @0
    @1
    @2
    @17
    @21
    simpll3
    cP
    @10
    cU
    snssg
    syl
    mpbird
    @19
    @20
    @12
    simprr
    @19
    @6
    @21
    @3
    @16
    @5
    @6
    simprrr
    adantr
    3jca
    ex
    reximdv
    mpd
    jca
    ex
    reximdv2
    mpd
end
