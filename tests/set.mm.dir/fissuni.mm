include "cuni.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wral.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wel.mm"
include "wex.mm"
include "simpr.mm"
include "dfss3.mm"
include "eluni2.mm"
include "ralbii.mm"
include "sylbb.mm"
include "adantr.mm"
include "eleq2.mm"
include "ac6sfi.mm"
include "syl2anc.mm"
include "cima.mm"
include "fimass.mm"
include "vex.mm"
include "imaex.mm"
include "elpw.mm"
include "sylibr.mm"
include "ad2antrl.mm"
include "wfun.mm"
include "ffun.mm"
include "simplr.mm"
include "imafi.mm"
include "elind.mm"
include "wfn.mm"
include "ffn.mm"
include "ssid.mm"
include "a1i.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "elssuni.mm"
include "syl.mm"
include "sseld.mm"
include "ralimdva.mm"
include "imp.mm"
include "adantl.mm"
include "wceq.mm"
include "unieq.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "exlimddv.mm"

theorem fissuni
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vf: setvar f
  let vx: setvar x
  let vz: setvar z

  disjoint A c
  disjoint B c
  disjoint A f
  disjoint c f
  disjoint A x
  disjoint B f
  disjoint B x
  disjoint B z
  disjoint x z
  disjoint f x
  disjoint f z
  assert |- ( ( A C_ U. B /\ A e. Fin ) -> E. c e. ( ~P B i^i Fin ) A C_ U. c )

  proof
    cA
    cB
    cuni
    #
    wss
    #
    cA
    cfn
    wcel
    #
    wa
    #
    cA
    cB
    vf
    cv
    #
    wf
    #
    vx
    cv
    #
    @6
    @4
    cfv
    #
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    cA
    vc
    cv
    #
    cuni
    #
    wss
    #
    vc
    cB
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vf
    @3
    @2
    vx
    vz
    wel
    #
    vz
    cB
    wrex
    #
    vx
    cA
    wral
    #
    @10
    vf
    wex
    @1
    @2
    simpr
    @1
    @19
    @2
    @1
    @6
    @0
    wcel
    #
    vx
    cA
    wral
    @19
    vx
    cA
    @0
    dfss3
    @20
    @18
    vx
    cA
    vz
    @6
    cB
    eluni2
    ralbii
    sylbb
    adantr
    @17
    @8
    vx
    vz
    cA
    cB
    vf
    vz
    cv
    @7
    @6
    eleq2
    ac6sfi
    syl2anc
    @3
    @10
    wa
    #
    @4
    cA
    cima
    #
    @15
    wcel
    cA
    @22
    cuni
    #
    wss
    #
    @16
    @21
    @14
    cfn
    @22
    @5
    @22
    @14
    wcel
    #
    @3
    @9
    @5
    @22
    cB
    wss
    @25
    cA
    cB
    @4
    cA
    fimass
    @22
    cB
    @4
    cA
    vf
    vex
    imaex
    elpw
    sylibr
    ad2antrl
    @21
    @4
    wfun
    #
    @2
    @22
    cfn
    wcel
    @5
    @26
    @3
    @9
    cA
    cB
    @4
    ffun
    ad2antrl
    @1
    @2
    @10
    simplr
    @4
    cA
    imafi
    syl2anc
    elind
    @10
    @24
    @3
    @10
    @6
    @23
    wcel
    #
    vx
    cA
    wral
    #
    @24
    @5
    @9
    @28
    @5
    @8
    @27
    vx
    cA
    @5
    @6
    cA
    wcel
    #
    wa
    #
    @7
    @23
    @6
    @30
    @7
    @22
    wcel
    #
    @7
    @23
    wss
    @30
    @4
    cA
    wfn
    #
    cA
    cA
    wss
    #
    @29
    @31
    @5
    @32
    @29
    cA
    cB
    @4
    ffn
    adantr
    @33
    @30
    cA
    ssid
    a1i
    @5
    @29
    simpr
    cA
    cA
    @4
    @6
    fnfvima
    syl3anc
    @7
    @22
    elssuni
    syl
    sseld
    ralimdva
    imp
    vx
    cA
    @23
    dfss3
    sylibr
    adantl
    @13
    @24
    vc
    @22
    @15
    @11
    @22
    wceq
    @12
    @23
    cA
    @11
    @22
    unieq
    sseq2d
    rspcev
    syl2anc
    exlimddv
end
