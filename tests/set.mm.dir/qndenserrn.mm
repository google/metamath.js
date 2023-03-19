include "cq.mm"
include "cmap.mm"
include "co.mm"
include "ccl.mm"
include "cfv.mm"
include "cr.mm"
include "cuni.mm"
include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "rrxtop.mm"
include "syl.mm"
include "cvv.mm"
include "reex.mm"
include "qssre.mm"
include "mapss.mm"
include "mp2an.mm"
include "a1i.mm"
include "crrx.mm"
include "cbs.mm"
include "ctopn.mm"
include "eqid.mm"
include "rrxbasefi.mm"
include "eqcomd.mm"
include "ctps.mm"
include "wceq.mm"
include "rrxtps.mm"
include "tpsuni.mm"
include "3syl.mm"
include "unieqi.mm"
include "eqcomi.mm"
include "3eqtrd.mm"
include "sseqtrd.mm"
include "clsss3.mm"
include "syl2anc.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wex.mm"
include "wrex.mm"
include "ad2antrr.mm"
include "id.mm"
include "syl6eleq.mm"
include "ad2antlr.mm"
include "ne0i.mm"
include "adantl.mm"
include "qndenserrnopn.mm"
include "df-rex.mm"
include "sylib.mm"
include "simpr.mm"
include "simpl.mm"
include "elind.mm"
include "eximdv.mm"
include "mpd.mm"
include "n0.mm"
include "sylibr.mm"
include "ex.mm"
include "adantlr.mm"
include "ralrimiva.mm"
include "wb.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "elcls.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "dfss3.mm"
include "eqssd.mm"

theorem qndenserrn
  let wph: wff ph
  let cI: class I
  let cJ: class J
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume qndenserrn.i: |- ( ph -> I e. Fin )
  assume qndenserrn.j: |- J = ( TopOpen ` ( RR^ ` I ) )


  assert |- ( ph -> ( ( cls ` J ) ` ( QQ ^m I ) ) = ( RR ^m I ) )

  proof
    wph
    cq
    cI
    cmap
    co
    #
    cJ
    ccl
    cfv
    cfv
    #
    cr
    cI
    cmap
    co
    #
    wph
    @1
    cJ
    cuni
    #
    @2
    wph
    cJ
    ctop
    wcel
    #
    @0
    @3
    wss
    #
    @1
    @3
    wss
    wph
    cI
    cfn
    wcel
    #
    @4
    qndenserrn.i
    cI
    cJ
    cfn
    qndenserrn.j
    rrxtop
    syl
    #
    wph
    @0
    @2
    @3
    @0
    @2
    wss
    #
    wph
    cr
    cvv
    wcel
    cq
    cr
    wss
    @8
    reex
    qssre
    cq
    cr
    cI
    cvv
    mapss
    mp2an
    a1i
    wph
    @2
    cI
    crrx
    cfv
    #
    cbs
    cfv
    #
    @9
    ctopn
    cfv
    #
    cuni
    #
    @3
    wph
    @10
    @2
    wph
    @10
    @9
    cI
    qndenserrn.i
    @9
    eqid
    @10
    eqid
    #
    rrxbasefi
    eqcomd
    wph
    @6
    @9
    ctps
    wcel
    @10
    @12
    wceq
    qndenserrn.i
    cI
    cfn
    rrxtps
    @10
    @11
    @9
    @13
    @11
    eqid
    #
    tpsuni
    3syl
    @12
    @3
    wceq
    wph
    @3
    @12
    cJ
    @11
    qndenserrn.j
    unieqi
    eqcomi
    a1i
    3eqtrd
    #
    sseqtrd
    #
    @0
    cJ
    @3
    @3
    eqid
    #
    clsss3
    syl2anc
    wph
    @2
    @3
    @15
    eqcomd
    sseqtrd
    wph
    vx
    cv
    #
    @1
    wcel
    #
    vx
    @2
    wral
    @2
    @1
    wss
    wph
    @19
    vx
    @2
    wph
    @18
    @2
    wcel
    #
    wa
    #
    @19
    @18
    vv
    cv
    #
    wcel
    #
    @22
    @0
    cin
    #
    c0
    wne
    #
    wi
    #
    vv
    cJ
    wral
    #
    @21
    @26
    vv
    cJ
    wph
    @22
    cJ
    wcel
    #
    @26
    @20
    wph
    @28
    wa
    #
    @23
    @25
    @29
    @23
    wa
    #
    vy
    cv
    #
    @24
    wcel
    #
    vy
    wex
    #
    @25
    @30
    @31
    @0
    wcel
    #
    @31
    @22
    wcel
    #
    wa
    #
    vy
    wex
    #
    @33
    @30
    @35
    vy
    @0
    wrex
    @37
    @30
    vy
    cI
    @11
    @22
    wph
    @6
    @28
    @23
    qndenserrn.i
    ad2antrr
    @14
    @28
    @22
    @11
    wcel
    wph
    @23
    @28
    @22
    cJ
    @11
    @28
    id
    qndenserrn.j
    syl6eleq
    ad2antlr
    @23
    @22
    c0
    wne
    @29
    @22
    @18
    ne0i
    adantl
    qndenserrnopn
    @35
    vy
    @0
    df-rex
    sylib
    @30
    @36
    @32
    vy
    @36
    @32
    wi
    @30
    @36
    @22
    @0
    @31
    @34
    @35
    simpr
    @34
    @35
    simpl
    elind
    a1i
    eximdv
    mpd
    vy
    @24
    n0
    sylibr
    ex
    adantlr
    ralrimiva
    @21
    @4
    @5
    @18
    @3
    wcel
    @19
    @27
    wb
    wph
    @4
    @20
    @7
    adantr
    wph
    @5
    @20
    @16
    adantr
    @21
    @18
    @2
    @3
    wph
    @20
    simpr
    wph
    @2
    @3
    wceq
    @20
    @15
    adantr
    eleqtrd
    vv
    @18
    @0
    cJ
    @3
    @17
    elcls
    syl3anc
    mpbird
    ralrimiva
    vx
    @2
    @1
    dfss3
    sylibr
    eqssd
end
