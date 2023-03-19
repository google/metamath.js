include "ccl.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "ctop.mm"
include "cuni.mm"
include "wss.mm"
include "wb.mm"
include "ctg.mm"
include "ctb.mm"
include "tgcl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "sseqtrd.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "elcls.mm"
include "syl3anc.mm"
include "bastg.mm"
include "sseqtr4d.mm"
include "sseld.mm"
include "imim1d.mm"
include "ralimdv2.mm"
include "wceq.mm"
include "eleq2.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "syl6ib.mm"
include "wa.mm"
include "wrex.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "tg2.mm"
include "syl2anc.mm"
include "rspccva.mm"
include "imp.mm"
include "ssdisj.mm"
include "ex.mm"
include "necon3d.mm"
include "syl5com.mm"
include "exp31.mm"
include "imp4a.mm"
include "rexlimdv.mm"
include "ad2antlr.mm"
include "mpd.mm"
include "exp43.mm"
include "ralrimdv.mm"
include "impbid.mm"
include "bitrd.mm"

theorem elcls3
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cS: class S
  let cJ: class J
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume elcls3.1: |- ( ph -> J = ( topGen ` B ) )
  assume elcls3.2: |- ( ph -> X = U. J )
  assume elcls3.3: |- ( ph -> B e. TopBases )
  assume elcls3.4: |- ( ph -> S C_ X )
  assume elcls3.5: |- ( ph -> P e. X )

  disjoint B x
  disjoint P x
  disjoint S x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint J y
  disjoint P y
  disjoint P z
  disjoint ph y
  disjoint S y
  disjoint S z
  assert |- ( ph -> ( P e. ( ( cls ` J ) ` S ) <-> A. x e. B ( P e. x -> ( x i^i S ) =/= (/) ) ) )

  proof
    wph
    cP
    cS
    cJ
    ccl
    cfv
    cfv
    wcel
    #
    cP
    vy
    cv
    #
    wcel
    #
    @1
    cS
    cin
    #
    c0
    wne
    #
    wi
    #
    vy
    cJ
    wral
    #
    cP
    vx
    cv
    #
    wcel
    #
    @7
    cS
    cin
    #
    c0
    wne
    #
    wi
    #
    vx
    cB
    wral
    #
    wph
    cJ
    ctop
    wcel
    cS
    cJ
    cuni
    #
    wss
    cP
    @13
    wcel
    @0
    @6
    wb
    wph
    cJ
    cB
    ctg
    cfv
    #
    ctop
    elcls3.1
    wph
    cB
    ctb
    wcel
    #
    @14
    ctop
    wcel
    elcls3.3
    cB
    tgcl
    syl
    eqeltrd
    wph
    cS
    cX
    @13
    elcls3.4
    elcls3.2
    sseqtrd
    wph
    cP
    cX
    @13
    elcls3.5
    elcls3.2
    eleqtrd
    vy
    cP
    cS
    cJ
    @13
    @13
    eqid
    elcls
    syl3anc
    wph
    @6
    @12
    wph
    @6
    @5
    vy
    cB
    wral
    @12
    wph
    @5
    @5
    vy
    cJ
    cB
    wph
    @1
    cB
    wcel
    @1
    cJ
    wcel
    #
    @5
    wph
    cB
    cJ
    @1
    wph
    cB
    @14
    cJ
    wph
    @15
    cB
    @14
    wss
    elcls3.3
    cB
    ctb
    bastg
    syl
    elcls3.1
    sseqtr4d
    sseld
    imim1d
    ralimdv2
    @5
    @11
    vy
    vx
    cB
    @1
    @7
    wceq
    #
    @2
    @8
    @4
    @10
    @1
    @7
    cP
    eleq2
    @17
    @3
    @9
    c0
    @1
    @7
    cS
    ineq1
    neeq1d
    imbi12d
    cbvralv
    syl6ib
    wph
    @12
    @5
    vy
    cJ
    wph
    @12
    @16
    @2
    @4
    wph
    @12
    wa
    #
    @16
    @2
    wa
    #
    wa
    #
    cP
    vz
    cv
    #
    wcel
    #
    @21
    @1
    wss
    #
    wa
    #
    vz
    cB
    wrex
    #
    @4
    @20
    @1
    @14
    wcel
    @2
    @25
    @20
    @1
    cJ
    @14
    @18
    @16
    @2
    simprl
    wph
    cJ
    @14
    wceq
    @12
    @19
    elcls3.1
    ad2antrr
    eleqtrd
    @18
    @16
    @2
    simprr
    vz
    @1
    cB
    cP
    tg2
    syl2anc
    @12
    @25
    @4
    wi
    wph
    @19
    @12
    @24
    @4
    vz
    cB
    @12
    @21
    cB
    wcel
    #
    @22
    @23
    @4
    @12
    @26
    @22
    @23
    @4
    wi
    @12
    @26
    wa
    #
    @22
    wa
    @21
    cS
    cin
    #
    c0
    wne
    #
    @23
    @4
    @27
    @22
    @29
    @11
    @22
    @29
    wi
    vx
    @21
    cB
    @7
    @21
    wceq
    #
    @8
    @22
    @10
    @29
    @7
    @21
    cP
    eleq2
    @30
    @9
    @28
    c0
    @7
    @21
    cS
    ineq1
    neeq1d
    imbi12d
    rspccva
    imp
    @23
    @3
    c0
    @28
    c0
    @23
    @3
    c0
    wceq
    @28
    c0
    wceq
    @21
    @1
    cS
    ssdisj
    ex
    necon3d
    syl5com
    exp31
    imp4a
    rexlimdv
    ad2antlr
    mpd
    exp43
    ralrimdv
    impbid
    bitrd
end
