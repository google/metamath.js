include "crest.mm"
include "co.mm"
include "cconn.mm"
include "wcel.mm"
include "cun.mm"
include "wss.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "w3a.mm"
include "wi.mm"
include "wral.mm"
include "wn.mm"
include "ctopon.mm"
include "cfv.mm"
include "wb.mm"
include "connsuba.mm"
include "syl2anc.mm"
include "3jca.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "3anbi13d.mm"
include "uneq1.mm"
include "imbi12d.mm"
include "ineq2.mm"
include "3anbi23d.mm"
include "sseqin2.mm"
include "necon3bbii.mm"
include "uneq2.mm"
include "sseq2d.mm"
include "notbid.mm"
include "syl5bbr.mm"
include "rspc2v.mm"
include "mpid.mm"
include "sylbid.mm"
include "mt2d.mm"

theorem nconnsubb
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cJ: class J
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume nconnsubb.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume nconnsubb.3: |- ( ph -> A C_ X )
  assume nconnsubb.4: |- ( ph -> U e. J )
  assume nconnsubb.5: |- ( ph -> V e. J )
  assume nconnsubb.6: |- ( ph -> ( U i^i A ) =/= (/) )
  assume nconnsubb.7: |- ( ph -> ( V i^i A ) =/= (/) )
  assume nconnsubb.8: |- ( ph -> ( ( U i^i V ) i^i A ) = (/) )
  assume nconnsubb.9: |- ( ph -> A C_ ( U u. V ) )


  assert |- ( ph -> -. ( J |`t A ) e. Conn )

  proof
    wph
    cJ
    cA
    crest
    co
    cconn
    wcel
    #
    cA
    cU
    cV
    cun
    #
    wss
    #
    nconnsubb.9
    wph
    @0
    vx
    cv
    #
    cA
    cin
    #
    c0
    wne
    #
    vy
    cv
    #
    cA
    cin
    #
    c0
    wne
    #
    @3
    @6
    cin
    #
    cA
    cin
    #
    c0
    wceq
    #
    w3a
    #
    @3
    @6
    cun
    #
    cA
    cin
    #
    cA
    wne
    #
    wi
    #
    vy
    cJ
    wral
    vx
    cJ
    wral
    #
    @2
    wn
    #
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cA
    cX
    wss
    @0
    @17
    wb
    nconnsubb.2
    nconnsubb.3
    vx
    vy
    cA
    cJ
    cX
    connsuba
    syl2anc
    wph
    @17
    cU
    cA
    cin
    #
    c0
    wne
    #
    cV
    cA
    cin
    #
    c0
    wne
    #
    cU
    cV
    cin
    #
    cA
    cin
    #
    c0
    wceq
    #
    w3a
    #
    @18
    wph
    @20
    @22
    @25
    nconnsubb.6
    nconnsubb.7
    nconnsubb.8
    3jca
    wph
    cU
    cJ
    wcel
    cV
    cJ
    wcel
    @17
    @26
    @18
    wi
    #
    wi
    nconnsubb.4
    nconnsubb.5
    @16
    @27
    @20
    @8
    cU
    @6
    cin
    #
    cA
    cin
    #
    c0
    wceq
    #
    w3a
    #
    cU
    @6
    cun
    #
    cA
    cin
    #
    cA
    wne
    #
    wi
    vx
    vy
    cU
    cV
    cJ
    cJ
    @3
    cU
    wceq
    #
    @12
    @31
    @15
    @34
    @35
    @5
    @20
    @11
    @30
    @8
    @35
    @4
    @19
    c0
    @3
    cU
    cA
    ineq1
    neeq1d
    @35
    @10
    @29
    c0
    @35
    @9
    @28
    cA
    @3
    cU
    @6
    ineq1
    ineq1d
    eqeq1d
    3anbi13d
    @35
    @14
    @33
    cA
    @35
    @13
    @32
    cA
    @3
    cU
    @6
    uneq1
    ineq1d
    neeq1d
    imbi12d
    @6
    cV
    wceq
    #
    @31
    @26
    @34
    @18
    @36
    @8
    @22
    @30
    @25
    @20
    @36
    @7
    @21
    c0
    @6
    cV
    cA
    ineq1
    neeq1d
    @36
    @29
    @24
    c0
    @36
    @28
    @23
    cA
    @6
    cV
    cU
    ineq2
    ineq1d
    eqeq1d
    3anbi23d
    @34
    cA
    @32
    wss
    #
    wn
    @36
    @18
    @37
    @33
    cA
    cA
    @32
    sseqin2
    necon3bbii
    @36
    @37
    @2
    @36
    @32
    @1
    cA
    @6
    cV
    cU
    uneq2
    sseq2d
    notbid
    syl5bbr
    imbi12d
    rspc2v
    syl2anc
    mpid
    sylbid
    mt2d
end
