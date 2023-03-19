include "cflim.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cuni.mm"
include "cfil.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "simp1l.mm"
include "eqid.mm"
include "flimfil.mm"
include "syl.mm"
include "csn.mm"
include "cnei.mm"
include "ctop.mm"
include "flimtop.mm"
include "simp2l.mm"
include "simp3l.mm"
include "opnneip.mm"
include "syl3anc.mm"
include "flimnei.mm"
include "syl2anc.mm"
include "simp1r.mm"
include "simp2r.mm"
include "simp3r.mm"
include "filinn0.mm"

theorem hausflimlem
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let cJ: class J
  let cV: class V
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let cS: class S
  let cX: class X


  assert |- ( ( ( A e. ( J fLim F ) /\ B e. ( J fLim F ) ) /\ ( U e. J /\ V e. J ) /\ ( A e. U /\ B e. V ) ) -> ( U i^i V ) =/= (/) )

  proof
    cA
    cJ
    cF
    cflim
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cU
    cJ
    wcel
    #
    cV
    cJ
    wcel
    #
    wa
    #
    cA
    cU
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    w3a
    #
    cF
    cJ
    cuni
    #
    cfil
    cfv
    wcel
    #
    cU
    cF
    wcel
    #
    cV
    cF
    wcel
    #
    cU
    cV
    cin
    c0
    wne
    @10
    @1
    @12
    @1
    @2
    @6
    @9
    simp1l
    #
    cA
    cF
    cJ
    @11
    @11
    eqid
    flimfil
    syl
    @10
    @1
    cU
    cA
    csn
    cJ
    cnei
    cfv
    #
    cfv
    wcel
    #
    @13
    @15
    @10
    cJ
    ctop
    wcel
    #
    @4
    @7
    @17
    @10
    @1
    @18
    @15
    cA
    cF
    cJ
    flimtop
    syl
    #
    @3
    @4
    @5
    @9
    simp2l
    @3
    @6
    @7
    @8
    simp3l
    cA
    cJ
    cU
    opnneip
    syl3anc
    cA
    cF
    cJ
    cU
    flimnei
    syl2anc
    @10
    @2
    cV
    cB
    csn
    @16
    cfv
    wcel
    #
    @14
    @1
    @2
    @6
    @9
    simp1r
    @10
    @18
    @5
    @8
    @20
    @19
    @3
    @4
    @5
    @9
    simp2r
    @3
    @6
    @7
    @8
    simp3r
    cB
    cJ
    cV
    opnneip
    syl3anc
    cB
    cF
    cJ
    cV
    flimnei
    syl2anc
    cU
    cV
    cF
    @11
    filinn0
    syl3anc
end
