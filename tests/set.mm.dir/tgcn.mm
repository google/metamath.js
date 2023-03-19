include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "wa.mm"
include "ctopon.mm"
include "cfv.mm"
include "wb.mm"
include "iscn.mm"
include "syl2anc.mm"
include "wss.mm"
include "wi.mm"
include "ctg.mm"
include "ctb.mm"
include "ctop.mm"
include "topontop.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "tgclb.mm"
include "sylibr.mm"
include "bastg.mm"
include "sseqtr4d.mm"
include "ssralv.mm"
include "cuni.mm"
include "wceq.mm"
include "wex.mm"
include "eleq2d.mm"
include "eltg3.mm"
include "bitrd.mm"
include "ciun.mm"
include "iunopn.mm"
include "ex.mm"
include "sylan9r.mm"
include "imaeq2.mm"
include "imauni.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "sylbid.mm"
include "imp.mm"
include "ralrimdva.mm"
include "cbvralv.mm"
include "syl6ib.mm"
include "impbid.mm"
include "anbi2d.mm"

theorem tgcn
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vz: setvar z
  let cP: class P
  assume tgcn.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume tgcn.3: |- ( ph -> K = ( topGen ` B ) )
  assume tgcn.4: |- ( ph -> K e. ( TopOn ` Y ) )

  disjoint B y
  disjoint F y
  disjoint J y
  disjoint K y
  disjoint X y
  disjoint Y y
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B z
  disjoint F x
  disjoint F z
  disjoint J x
  disjoint J z
  disjoint K x
  disjoint K z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint ph x
  disjoint ph z
  disjoint X x
  disjoint X z
  disjoint Y x
  disjoint Y z
  assert |- ( ph -> ( F e. ( J Cn K ) <-> ( F : X --> Y /\ A. y e. B ( `' F " y ) e. J ) ) )

  proof
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cF
    ccnv
    #
    vy
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vy
    cK
    wral
    #
    wa
    #
    @1
    @5
    vy
    cB
    wral
    #
    wa
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @0
    @7
    wb
    tgcn.1
    tgcn.4
    vy
    cF
    cJ
    cK
    cX
    cY
    iscn
    syl2anc
    wph
    @6
    @8
    @1
    wph
    @6
    @8
    wph
    cB
    cK
    wss
    @6
    @8
    wi
    wph
    cB
    cB
    ctg
    cfv
    #
    cK
    wph
    cB
    ctb
    wcel
    #
    cB
    @11
    wss
    wph
    @11
    ctop
    wcel
    @12
    wph
    cK
    @11
    ctop
    tgcn.3
    wph
    @10
    cK
    ctop
    wcel
    tgcn.4
    cY
    cK
    topontop
    syl
    eqeltrrd
    cB
    tgclb
    sylibr
    #
    cB
    ctb
    bastg
    syl
    tgcn.3
    sseqtr4d
    @5
    vy
    cB
    cK
    ssralv
    syl
    wph
    @8
    @2
    vx
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vx
    cK
    wral
    @6
    wph
    @8
    @16
    vx
    cK
    wph
    @14
    cK
    wcel
    #
    @8
    @16
    wi
    #
    wph
    @17
    vz
    cv
    #
    cB
    wss
    #
    @14
    @19
    cuni
    #
    wceq
    #
    wa
    #
    vz
    wex
    #
    @18
    wph
    @17
    @14
    @11
    wcel
    #
    @24
    wph
    cK
    @11
    @14
    tgcn.3
    eleq2d
    wph
    @12
    @25
    @24
    wb
    @13
    vz
    @14
    cB
    ctb
    eltg3
    syl
    bitrd
    wph
    @23
    @18
    vz
    wph
    @20
    @22
    @18
    wph
    @20
    wa
    @18
    @22
    @8
    vy
    @19
    @4
    ciun
    #
    cJ
    wcel
    #
    wi
    @20
    @8
    @5
    vy
    @19
    wral
    #
    wph
    @27
    @5
    vy
    @19
    cB
    ssralv
    wph
    cJ
    ctop
    wcel
    #
    @28
    @27
    wi
    wph
    @9
    @29
    tgcn.1
    cX
    cJ
    topontop
    syl
    @29
    @28
    @27
    vy
    @19
    @4
    cJ
    iunopn
    ex
    syl
    sylan9r
    @22
    @16
    @27
    @8
    @22
    @15
    @26
    cJ
    @22
    @15
    @2
    @21
    cima
    @26
    @14
    @21
    @2
    imaeq2
    vy
    @2
    @19
    imauni
    syl6eq
    eleq1d
    imbi2d
    syl5ibrcom
    expimpd
    exlimdv
    sylbid
    imp
    ralrimdva
    @16
    @5
    vx
    vy
    cK
    @14
    @3
    wceq
    @15
    @4
    cJ
    @14
    @3
    @2
    imaeq2
    eleq1d
    cbvralv
    syl6ib
    impbid
    anbi2d
    bitrd
end
