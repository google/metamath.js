include "cico.mm"
include "co.mm"
include "cmap.mm"
include "wcel.mm"
include "wf.mm"
include "cxr.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "ovexd.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "id.mm"
include "wss.mm"
include "icossxr.mm"
include "a1i.mm"
include "fssd.mm"
include "ffvelrn.mm"
include "ralrimiva.mm"
include "jca.mm"
include "wfn.mm"
include "ffn.mm"
include "adantr.mm"
include "simpr.mm"
include "ffnfv.mm"
include "sylibr.mm"
include "impbii.mm"
include "bitrd.mm"

theorem elhoi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume elhoi.1: |- ( ph -> X e. V )

  disjoint A x
  disjoint B x
  disjoint X x
  disjoint Y x
  disjoint k x
  assert |- ( ph -> ( Y e. ( ( A [,) B ) ^m X ) <-> ( Y : X --> RR* /\ A. x e. X ( Y ` x ) e. ( A [,) B ) ) ) )

  proof
    wph
    cY
    cA
    cB
    cico
    co
    #
    cX
    cmap
    co
    wcel
    #
    cX
    @0
    cY
    wf
    #
    cX
    cxr
    cY
    wf
    #
    vx
    cv
    #
    cY
    cfv
    @0
    wcel
    #
    vx
    cX
    wral
    #
    wa
    #
    wph
    @0
    cvv
    wcel
    cX
    cV
    wcel
    @1
    @2
    wb
    wph
    cA
    cB
    cico
    ovexd
    elhoi.1
    @0
    cX
    cY
    cvv
    cV
    elmapg
    syl2anc
    @2
    @7
    wb
    wph
    @2
    @7
    @2
    @3
    @6
    @2
    cX
    @0
    cxr
    cY
    @2
    id
    @0
    cxr
    wss
    @2
    cA
    cB
    icossxr
    a1i
    fssd
    @2
    @5
    vx
    cX
    cX
    @0
    @4
    cY
    ffvelrn
    ralrimiva
    jca
    @7
    cY
    cX
    wfn
    #
    @6
    wa
    @2
    @7
    @8
    @6
    @3
    @8
    @6
    cX
    cxr
    cY
    ffn
    adantr
    @3
    @6
    simpr
    jca
    vx
    cX
    @0
    cY
    ffnfv
    sylibr
    impbii
    a1i
    bitrd
end
