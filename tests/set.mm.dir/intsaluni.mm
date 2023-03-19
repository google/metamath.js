include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "cint.mm"
include "cuni.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "biimpi.mm"
include "syl.mm"
include "nfv.mm"
include "wa.mm"
include "wss.mm"
include "intss1.mm"
include "uniss.mm"
include "adantl.mm"
include "sseqtrd.mm"
include "wral.mm"
include "wrex.mm"
include "adantr.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "eqcomd.mm"
include "adantlr.mm"
include "eqtrd.mm"
include "csalg.mm"
include "sselda.mm"
include "saluni.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wb.mm"
include "uniexg.mm"
include "elintg.mm"
include "mpbird.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "eleq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eluni2.mm"
include "sylibr.mm"
include "dfss3.mm"
include "eqssd.mm"
include "ex.mm"
include "exlimd.mm"
include "mpd.mm"

theorem intsaluni
  let wph: wff ph
  let cG: class G
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume intsaluni.ga: |- ( ph -> G C_ SAlg )
  assume intsaluni.gn0: |- ( ph -> G =/= (/) )
  assume intsaluni.x: |- ( ( ph /\ s e. G ) -> U. s = X )

  disjoint G s
  disjoint X s
  disjoint ph s
  disjoint G t
  disjoint s t
  disjoint G x
  disjoint G y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint X x
  disjoint ph t
  disjoint ph x
  disjoint k x
  assert |- ( ph -> U. |^| G = X )

  proof
    wph
    vs
    cv
    #
    cG
    wcel
    #
    vs
    wex
    #
    cG
    cint
    #
    cuni
    #
    cX
    wceq
    #
    wph
    cG
    c0
    wne
    #
    @2
    intsaluni.gn0
    @6
    @2
    vs
    cG
    n0
    biimpi
    syl
    wph
    @1
    @5
    vs
    wph
    vs
    nfv
    @5
    vs
    nfv
    wph
    @1
    @5
    wph
    @1
    wa
    #
    @4
    cX
    @7
    @4
    @0
    cuni
    #
    cX
    @1
    @4
    @8
    wss
    #
    wph
    @1
    @3
    @0
    wss
    @9
    @0
    cG
    intss1
    @3
    @0
    uniss
    syl
    adantl
    intsaluni.x
    sseqtrd
    @7
    vx
    cv
    #
    @4
    wcel
    #
    vx
    cX
    wral
    cX
    @4
    wss
    @7
    @11
    vx
    cX
    @7
    @10
    cX
    wcel
    #
    wa
    #
    @10
    vy
    cv
    #
    wcel
    #
    vy
    @3
    wrex
    #
    @11
    @13
    @8
    @3
    wcel
    #
    @10
    @8
    wcel
    #
    @16
    @7
    @17
    @12
    @7
    @17
    @8
    vt
    cv
    #
    wcel
    #
    vt
    cG
    wral
    #
    @7
    @20
    vt
    cG
    @7
    @19
    cG
    wcel
    #
    wa
    #
    @8
    @19
    cuni
    #
    @19
    @23
    @8
    cX
    @24
    @7
    @8
    cX
    wceq
    #
    @22
    intsaluni.x
    adantr
    wph
    @22
    cX
    @24
    wceq
    @1
    wph
    @22
    wa
    #
    @24
    cX
    @7
    @25
    wi
    @26
    @24
    cX
    wceq
    #
    wi
    vs
    vt
    @0
    @19
    wceq
    #
    @7
    @26
    @25
    @27
    @28
    @1
    @22
    wph
    @0
    @19
    cG
    eleq1
    anbi2d
    @28
    @8
    @24
    cX
    @0
    @19
    unieq
    eqeq1d
    imbi12d
    intsaluni.x
    chvarv
    eqcomd
    adantlr
    eqtrd
    wph
    @22
    @24
    @19
    wcel
    #
    @1
    @26
    @19
    csalg
    wcel
    @29
    wph
    cG
    csalg
    @19
    intsaluni.ga
    sselda
    @19
    saluni
    syl
    adantlr
    eqeltrd
    ralrimiva
    @7
    @8
    cvv
    wcel
    #
    @17
    @21
    wb
    @1
    @30
    wph
    @0
    cG
    uniexg
    adantl
    vt
    @8
    cG
    cvv
    elintg
    syl
    mpbird
    adantr
    @13
    @10
    cX
    @8
    @7
    @12
    simpr
    @7
    cX
    @8
    wceq
    @12
    @7
    @8
    cX
    intsaluni.x
    eqcomd
    adantr
    eleqtrd
    @15
    @18
    vy
    @8
    @3
    @14
    @8
    @10
    eleq2
    rspcev
    syl2anc
    vy
    @10
    @3
    eluni2
    sylibr
    ralrimiva
    vx
    cX
    @4
    dfss3
    sylibr
    eqssd
    ex
    exlimd
    mpd
end
