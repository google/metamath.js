include "cv.mm"
include "cfv.mm"
include "cprod.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "csn.mm"
include "cdif.mm"
include "cmul.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "cfn.mm"
include "adantr.mm"
include "diffi.mm"
include "syl.mm"
include "wf.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "adantlr.mm"
include "fprodzcl.mm"
include "dvdsmul2.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "neldifsnd.mm"
include "disjsn.mm"
include "sylibr.mm"
include "cun.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "adantl.mm"
include "wss.mm"
include "zcnd.mm"
include "fprodsplit.mm"
include "cc.mm"
include "simpr.mm"
include "fveq2.mm"
include "prodsn.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "ralbidva.mm"
include "mpbird.mm"

theorem fprodfvdvdsd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  assume fprodfvdvdsd.a: |- ( ph -> A e. Fin )
  assume fprodfvdvdsd.b: |- ( ph -> A C_ B )
  assume fprodfvdvdsd.f: |- ( ph -> F : B --> ZZ )

  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> A. x e. A ( F ` x ) || prod_ k e. A ( F ` k ) )

  proof
    wph
    vx
    cv
    #
    cF
    cfv
    #
    cA
    vk
    cv
    #
    cF
    cfv
    #
    vk
    cprod
    #
    cdvds
    wbr
    #
    vx
    cA
    wral
    @1
    cA
    @0
    csn
    #
    cdif
    #
    @3
    vk
    cprod
    #
    @1
    cmul
    co
    #
    cdvds
    wbr
    #
    vx
    cA
    wral
    wph
    @10
    vx
    cA
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @8
    cz
    wcel
    @1
    cz
    wcel
    @10
    @12
    @7
    @3
    vk
    @12
    cA
    cfn
    wcel
    #
    @7
    cfn
    wcel
    wph
    @13
    @11
    fprodfvdvdsd.a
    adantr
    #
    cA
    @6
    diffi
    syl
    wph
    @2
    @7
    wcel
    #
    @3
    cz
    wcel
    @11
    wph
    @15
    wa
    cB
    cz
    @2
    cF
    wph
    cB
    cz
    cF
    wf
    #
    @15
    fprodfvdvdsd.f
    adantr
    wph
    @7
    cB
    @2
    wph
    cA
    cB
    @6
    fprodfvdvdsd.b
    ssdifssd
    sselda
    ffvelrnd
    adantlr
    fprodzcl
    @12
    cB
    cz
    @0
    cF
    wph
    @16
    @11
    fprodfvdvdsd.f
    adantr
    #
    wph
    cA
    cB
    @0
    fprodfvdvdsd.b
    sselda
    ffvelrnd
    #
    @8
    @1
    dvdsmul2
    syl2anc
    ralrimiva
    wph
    @5
    @10
    vx
    cA
    @12
    @4
    @9
    @1
    cdvds
    @12
    @4
    @8
    @6
    @3
    vk
    cprod
    #
    cmul
    co
    @9
    @12
    @7
    @6
    @3
    cA
    vk
    @12
    @0
    @7
    wcel
    wn
    @7
    @6
    cin
    c0
    wceq
    @12
    @0
    cA
    neldifsnd
    @7
    @0
    disjsn
    sylibr
    @11
    cA
    @7
    @6
    cun
    #
    wceq
    wph
    @11
    @20
    cA
    cA
    @0
    difsnid
    eqcomd
    adantl
    @14
    @12
    @2
    cA
    wcel
    #
    wa
    #
    @3
    @22
    cB
    cz
    @2
    cF
    @12
    @16
    @21
    @17
    adantr
    @12
    cA
    cB
    @2
    wph
    cA
    cB
    wss
    @11
    fprodfvdvdsd.b
    adantr
    sselda
    ffvelrnd
    zcnd
    fprodsplit
    @12
    @19
    @1
    @8
    cmul
    @12
    @11
    @1
    cc
    wcel
    @19
    @1
    wceq
    wph
    @11
    simpr
    @12
    @1
    @18
    zcnd
    @3
    @1
    vk
    @0
    cA
    @2
    @0
    cF
    fveq2
    prodsn
    syl2anc
    oveq2d
    eqtrd
    breq2d
    ralbidva
    mpbird
end
