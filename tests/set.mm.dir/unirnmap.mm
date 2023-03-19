include "cv.mm"
include "cuni.mm"
include "crn.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "wfn.mm"
include "cfv.mm"
include "sselda.mm"
include "elmapfn.mm"
include "syl.mm"
include "ciun.mm"
include "wrex.mm"
include "simplr.mm"
include "dffn3.mm"
include "sylib.mm"
include "ffvelrnda.mm"
include "wceq.mm"
include "rneq.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eliun.mm"
include "sylibr.mm"
include "rnuni.mm"
include "syl6eleqr.mm"
include "ralrimiva.mm"
include "jca.mm"
include "ffnfv.mm"
include "wb.mm"
include "cvv.mm"
include "ovexd.mm"
include "ssexd.mm"
include "uniexg.mm"
include "rnexg.mm"
include "elmapd.mm"
include "adantr.mm"
include "mpbird.mm"
include "dfss3.mm"

theorem unirnmap
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  let cX: class X
  let vg: setvar g
  let vx: setvar x
  let vf: setvar f
  assume unirnmap.a: |- ( ph -> A e. V )
  assume unirnmap.x: |- ( ph -> X C_ ( B ^m A ) )


  assert |- ( ph -> X C_ ( ran U. X ^m A ) )

  proof
    wph
    vg
    cv
    #
    cX
    cuni
    #
    crn
    #
    cA
    cmap
    co
    #
    wcel
    #
    vg
    cX
    wral
    cX
    @3
    wss
    wph
    @4
    vg
    cX
    wph
    @0
    cX
    wcel
    #
    wa
    #
    @4
    cA
    @2
    @0
    wf
    #
    @6
    @0
    cA
    wfn
    #
    vx
    cv
    #
    @0
    cfv
    #
    @2
    wcel
    #
    vx
    cA
    wral
    #
    wa
    @7
    @6
    @8
    @12
    @6
    @0
    cB
    cA
    cmap
    co
    #
    wcel
    @8
    wph
    cX
    @13
    @0
    unirnmap.x
    sselda
    @0
    cB
    cA
    elmapfn
    syl
    #
    @6
    @11
    vx
    cA
    @6
    @9
    cA
    wcel
    #
    wa
    #
    @10
    vf
    cX
    vf
    cv
    #
    crn
    #
    ciun
    #
    @2
    @16
    @10
    @18
    wcel
    #
    vf
    cX
    wrex
    #
    @10
    @19
    wcel
    @16
    @5
    @10
    @0
    crn
    #
    wcel
    #
    @21
    wph
    @5
    @15
    simplr
    @6
    cA
    @22
    @9
    @0
    @6
    @8
    cA
    @22
    @0
    wf
    @14
    cA
    @0
    dffn3
    sylib
    ffvelrnda
    @20
    @23
    vf
    @0
    cX
    @17
    @0
    wceq
    @18
    @22
    @10
    @17
    @0
    rneq
    eleq2d
    rspcev
    syl2anc
    vf
    @10
    cX
    @18
    eliun
    sylibr
    vf
    cX
    rnuni
    syl6eleqr
    ralrimiva
    jca
    vx
    cA
    @2
    @0
    ffnfv
    sylibr
    wph
    @4
    @7
    wb
    @5
    wph
    @2
    cA
    @0
    cvv
    cV
    wph
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    wph
    cX
    cvv
    wcel
    @24
    wph
    cX
    @13
    cvv
    wph
    cB
    cA
    cmap
    ovexd
    unirnmap.x
    ssexd
    cX
    cvv
    uniexg
    syl
    @1
    cvv
    rnexg
    syl
    unirnmap.a
    elmapd
    adantr
    mpbird
    ralrimiva
    vg
    cX
    @3
    dfss3
    sylibr
end
