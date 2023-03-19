include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cuni.mm"
include "cesum.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "resmptf.mm"
include "syl.mm"
include "oveq2d.mm"
include "xrge0base.mm"
include "xrge00.mm"
include "ccmn.mm"
include "wcel.mm"
include "xrge0cmn.mm"
include "a1i.mm"
include "ctps.mm"
include "xrge0tps.mm"
include "nfcv.mm"
include "eqid.mm"
include "fmptdF.mm"
include "suppss2f.mm"
include "tsmsres.mm"
include "eqtr3d.mm"
include "unieqd.mm"
include "df-esum.mm"
include "3eqtr4g.mm"

theorem esumss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  assume esumss.p: |- F/ k ph
  assume esumss.a: |- F/_ k A
  assume esumss.b: |- F/_ k B
  assume esumss.1: |- ( ph -> A C_ B )
  assume esumss.2: |- ( ph -> B e. V )
  assume esumss.3: |- ( ( ph /\ k e. B ) -> C e. ( 0 [,] +oo ) )
  assume esumss.4: |- ( ( ph /\ k e. ( B \ A ) ) -> C = 0 )


  assert |- ( ph -> sum* k e. A C = sum* k e. B C )

  proof
    wph
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    vk
    cA
    cC
    cmpt
    #
    ctsu
    co
    #
    cuni
    @1
    vk
    cB
    cC
    cmpt
    #
    ctsu
    co
    #
    cuni
    cA
    cC
    vk
    cesum
    cB
    cC
    vk
    cesum
    wph
    @3
    @5
    wph
    @1
    @4
    cA
    cres
    #
    ctsu
    co
    @3
    @5
    wph
    @6
    @2
    @1
    ctsu
    wph
    cA
    cB
    wss
    @6
    @2
    wceq
    esumss.1
    vk
    cB
    cA
    cC
    esumss.b
    esumss.a
    resmptf
    syl
    oveq2d
    wph
    cB
    @0
    @4
    @1
    cV
    cA
    cc0
    xrge0base
    xrge00
    @1
    ccmn
    wcel
    wph
    xrge0cmn
    a1i
    @1
    ctps
    wcel
    wph
    xrge0tps
    a1i
    esumss.2
    wph
    vk
    cB
    cC
    @0
    @4
    esumss.p
    esumss.b
    vk
    @0
    nfcv
    esumss.3
    @4
    eqid
    fmptdF
    wph
    cB
    cC
    vk
    cV
    cA
    cc0
    esumss.p
    esumss.b
    esumss.a
    esumss.4
    esumss.2
    suppss2f
    tsmsres
    eqtr3d
    unieqd
    cA
    cC
    vk
    df-esum
    cB
    cC
    vk
    df-esum
    3eqtr4g
end
