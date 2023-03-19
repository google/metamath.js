include "ciin.mm"
include "cin.mm"
include "csn.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cint.mm"
include "c0.mm"
include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wral.mm"
include "wceq.mm"
include "ctop.mm"
include "ccmp.mm"
include "cmptop.mm"
include "syl.mm"
include "topcld.mm"
include "cv.mm"
include "wa.mm"
include "cldss.mm"
include "ralrimiva.mm"
include "riinint.mm"
include "syl2anc.mm"
include "cfi.mm"
include "wn.mm"
include "wne.mm"
include "snssd.mm"
include "wf.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "unssd.mm"
include "cpw.mm"
include "cfn.mm"
include "wrex.mm"
include "elin.mm"
include "elpwi.mm"
include "anim1i.mm"
include "sylbi.mm"
include "nesym.mm"
include "sylib.mm"
include "sylan2.mm"
include "nrexdv.mm"
include "wb.mm"
include "elrfirn2.mm"
include "mtbird.mm"
include "cmpfii.mm"
include "syl3anc.mm"
include "eqnetrd.mm"

theorem cmpfiiin
  let wph: wff ph
  let cS: class S
  let vk: setvar k
  let cI: class I
  let cJ: class J
  let cX: class X
  let vl: setvar l
  assume cmpfiiin.x: |- X = U. J
  assume cmpfiiin.j: |- ( ph -> J e. Comp )
  assume cmpfiiin.s: |- ( ( ph /\ k e. I ) -> S e. ( Clsd ` J ) )
  assume cmpfiiin.z: |- ( ( ph /\ ( l C_ I /\ l e. Fin ) ) -> ( X i^i |^|_ k e. l S ) =/= (/) )

  disjoint k ph
  disjoint l ph
  disjoint k l
  disjoint I k
  disjoint I l
  disjoint J k
  disjoint J l
  disjoint S l
  disjoint X k
  disjoint X l
  assert |- ( ph -> ( X i^i |^|_ k e. I S ) =/= (/) )

  proof
    wph
    cX
    vk
    cI
    cS
    ciin
    cin
    #
    cX
    csn
    #
    vk
    cI
    cS
    cmpt
    #
    crn
    #
    cun
    #
    cint
    #
    c0
    wph
    cX
    cJ
    ccld
    cfv
    #
    wcel
    #
    cS
    cX
    wss
    #
    vk
    cI
    wral
    #
    @0
    @5
    wceq
    wph
    cJ
    ctop
    wcel
    #
    @7
    wph
    cJ
    ccmp
    wcel
    #
    @10
    cmpfiiin.j
    cJ
    cmptop
    syl
    cJ
    cX
    cmpfiiin.x
    topcld
    syl
    #
    wph
    @8
    vk
    cI
    wph
    vk
    cv
    cI
    wcel
    wa
    cS
    @6
    wcel
    @8
    cmpfiiin.s
    cS
    cJ
    cX
    cmpfiiin.x
    cldss
    syl
    ralrimiva
    #
    cS
    vk
    cI
    @6
    cX
    riinint
    syl2anc
    wph
    @11
    @4
    @6
    wss
    c0
    @4
    cfi
    cfv
    wcel
    #
    wn
    @5
    c0
    wne
    cmpfiiin.j
    wph
    @1
    @3
    @6
    wph
    cX
    @6
    @12
    snssd
    wph
    cI
    @6
    @2
    wf
    @3
    @6
    wss
    wph
    vk
    cI
    cS
    @6
    @2
    cmpfiiin.s
    @2
    eqid
    fmptd
    cI
    @6
    @2
    frn
    syl
    unssd
    wph
    @14
    c0
    cX
    vk
    vl
    cv
    #
    cS
    ciin
    cin
    #
    wceq
    #
    vl
    cI
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wph
    @17
    vl
    @19
    @15
    @19
    wcel
    #
    wph
    @15
    cI
    wss
    #
    @15
    cfn
    wcel
    #
    wa
    #
    @17
    wn
    #
    @21
    @15
    @18
    wcel
    #
    @23
    wa
    @24
    @15
    @18
    cfn
    elin
    @26
    @22
    @23
    @15
    cI
    elpwi
    anim1i
    sylbi
    wph
    @24
    wa
    @16
    c0
    wne
    @25
    cmpfiiin.z
    @16
    c0
    nesym
    sylib
    sylan2
    nrexdv
    wph
    @7
    @9
    @14
    @20
    wb
    @12
    @13
    vk
    vl
    c0
    cX
    cS
    cI
    @6
    elrfirn2
    syl2anc
    mtbird
    cJ
    @4
    cmpfii
    syl3anc
    eqnetrd
end
