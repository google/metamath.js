include "c0.mm"
include "wne.mm"
include "cun.mm"
include "wceq.mm"
include "cdif.mm"
include "wss.mm"
include "cin.mm"
include "wb.mm"
include "cuni.mm"
include "wcel.mm"
include "elssuni.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "uneqdifeq.mm"
include "syl2anc.mm"
include "wa.mm"
include "simpr.mm"
include "difeq2d.mm"
include "dfss4.mm"
include "sylib.mm"
include "adantr.mm"
include "cconn.mm"
include "ccld.mm"
include "cfv.mm"
include "ctop.mm"
include "cpr.mm"
include "isconn.mm"
include "simplbi.mm"
include "opncld.mm"
include "eqeltrrd.mm"
include "connclo.mm"
include "difid.mm"
include "syl6eq.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "sylbid.mm"
include "necon3d.mm"
include "mpd.mm"

theorem conndisj
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  let vj: setvar j
  assume isconn.1: |- X = U. J
  assume connclo.1: |- ( ph -> J e. Conn )
  assume connclo.2: |- ( ph -> A e. J )
  assume connclo.3: |- ( ph -> A =/= (/) )
  assume conndisj.4: |- ( ph -> B e. J )
  assume conndisj.5: |- ( ph -> B =/= (/) )
  assume conndisj.6: |- ( ph -> ( A i^i B ) = (/) )


  assert |- ( ph -> ( A u. B ) =/= X )

  proof
    wph
    cA
    c0
    wne
    cA
    cB
    cun
    #
    cX
    wne
    connclo.3
    wph
    @0
    cX
    cA
    c0
    wph
    @0
    cX
    wceq
    #
    cX
    cA
    cdif
    #
    cB
    wceq
    #
    cA
    c0
    wceq
    #
    wph
    cA
    cX
    wss
    #
    cA
    cB
    cin
    c0
    wceq
    @1
    @3
    wb
    wph
    cA
    cJ
    cuni
    #
    cX
    wph
    cA
    cJ
    wcel
    #
    cA
    @6
    wss
    connclo.2
    cA
    cJ
    elssuni
    syl
    isconn.1
    syl6sseqr
    #
    conndisj.6
    cA
    cB
    cX
    uneqdifeq
    syl2anc
    wph
    @3
    @4
    wph
    @3
    wa
    #
    cX
    @2
    cdif
    #
    cX
    cB
    cdif
    #
    cA
    c0
    @9
    @2
    cB
    cX
    wph
    @3
    simpr
    #
    difeq2d
    wph
    @10
    cA
    wceq
    #
    @3
    wph
    @5
    @13
    @8
    cA
    cX
    dfss4
    sylib
    adantr
    @9
    @11
    cX
    cX
    cdif
    c0
    @9
    cB
    cX
    cX
    @9
    cB
    cJ
    cX
    isconn.1
    wph
    cJ
    cconn
    wcel
    #
    @3
    connclo.1
    adantr
    wph
    cB
    cJ
    wcel
    @3
    conndisj.4
    adantr
    wph
    cB
    c0
    wne
    @3
    conndisj.5
    adantr
    @9
    @2
    cB
    cJ
    ccld
    cfv
    #
    @12
    wph
    @2
    @15
    wcel
    #
    @3
    wph
    cJ
    ctop
    wcel
    #
    @7
    @16
    wph
    @14
    @17
    connclo.1
    @14
    @17
    cJ
    @15
    cin
    c0
    cX
    cpr
    wceq
    cJ
    cX
    isconn.1
    isconn
    simplbi
    syl
    connclo.2
    cA
    cJ
    cX
    isconn.1
    opncld
    syl2anc
    adantr
    eqeltrrd
    connclo
    difeq2d
    cX
    difid
    syl6eq
    3eqtr3d
    ex
    sylbid
    necon3d
    mpd
end
