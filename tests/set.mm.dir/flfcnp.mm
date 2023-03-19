include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "w3a.mm"
include "cflf.mm"
include "co.mm"
include "ccnp.mm"
include "wa.mm"
include "cfm.mm"
include "ccom.mm"
include "cflim.mm"
include "simprl.mm"
include "wceq.mm"
include "flfval.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "simprr.mm"
include "cnpflfi.mm"
include "syl2anc.mm"
include "cuni.mm"
include "cfbas.mm"
include "ctop.mm"
include "cnptop2.mm"
include "ad2antll.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "toponmax.mm"
include "syl.mm"
include "simpl1.mm"
include "simpl2.mm"
include "filfbas.mm"
include "cnpf2.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "fmco.mm"
include "syl32anc.mm"
include "oveq2d.mm"
include "fco.mm"
include "fmfil.mm"
include "3eqtr4d.mm"
include "eleqtrrd.mm"

theorem flfcnp
  let cA: class A
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y


  assert |- ( ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) /\ F : Y --> X ) /\ ( A e. ( ( J fLimf L ) ` F ) /\ G e. ( ( J CnP K ) ` A ) ) ) -> ( G ` A ) e. ( ( K fLimf L ) ` ( G o. F ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cL
    cY
    cfil
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cA
    cF
    cJ
    cL
    cflf
    co
    cfv
    #
    wcel
    #
    cG
    cA
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    wa
    #
    wa
    #
    cA
    cG
    cfv
    #
    cG
    cK
    cL
    cX
    cF
    cfm
    co
    cfv
    #
    cflf
    co
    cfv
    #
    cG
    cF
    ccom
    #
    cK
    cL
    cflf
    co
    cfv
    #
    @8
    cA
    cJ
    @10
    cflim
    co
    #
    wcel
    @6
    @9
    @11
    wcel
    @8
    cA
    @4
    @14
    @3
    @5
    @6
    simprl
    @3
    @4
    @14
    wceq
    @7
    cF
    cJ
    cL
    cX
    cY
    flfval
    adantr
    eleqtrd
    @3
    @5
    @6
    simprr
    #
    cA
    cG
    cJ
    cK
    @10
    cnpflfi
    syl2anc
    @8
    cK
    cL
    cK
    cuni
    #
    @12
    cfm
    co
    cfv
    #
    cflim
    co
    #
    cK
    @10
    @16
    cG
    cfm
    co
    cfv
    #
    cflim
    co
    #
    @13
    @11
    @8
    @17
    @19
    cK
    cflim
    @8
    @16
    cK
    wcel
    #
    cX
    cJ
    wcel
    #
    cL
    cY
    cfbas
    cfv
    wcel
    #
    cX
    @16
    cG
    wf
    #
    @2
    @17
    @19
    wceq
    @8
    cK
    @16
    ctopon
    cfv
    wcel
    #
    @21
    @8
    cK
    ctop
    wcel
    #
    @25
    @6
    @26
    @3
    @5
    cA
    cG
    cJ
    cK
    cnptop2
    ad2antll
    cK
    @16
    @16
    eqid
    toptopon
    sylib
    #
    @16
    cK
    toponmax
    syl
    @8
    @0
    @22
    @0
    @1
    @2
    @7
    simpl1
    #
    cX
    cJ
    toponmax
    syl
    #
    @8
    @1
    @23
    @0
    @1
    @2
    @7
    simpl2
    #
    cL
    cY
    filfbas
    syl
    #
    @8
    @0
    @25
    @6
    @24
    @28
    @27
    @15
    cA
    cG
    cJ
    cK
    cX
    @16
    cnpf2
    syl3anc
    #
    @0
    @1
    @2
    @7
    simpl3
    #
    cL
    cG
    cF
    cK
    cJ
    @16
    cX
    cY
    fmco
    syl32anc
    oveq2d
    @8
    @25
    @1
    cY
    @16
    @12
    wf
    #
    @13
    @18
    wceq
    @27
    @30
    @8
    @24
    @2
    @34
    @32
    @33
    cY
    cX
    @16
    cG
    cF
    fco
    syl2anc
    @12
    cK
    cL
    @16
    cY
    flfval
    syl3anc
    @8
    @25
    @10
    cX
    cfil
    cfv
    wcel
    #
    @24
    @11
    @20
    wceq
    @27
    @8
    @22
    @23
    @2
    @35
    @29
    @31
    @33
    cJ
    cL
    cF
    cX
    cY
    fmfil
    syl3anc
    @32
    cG
    cK
    @10
    @16
    cX
    flfval
    syl3anc
    3eqtr4d
    eleqtrrd
end
