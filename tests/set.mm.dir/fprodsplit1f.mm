include "cprod.mm"
include "csn.mm"
include "cdif.mm"
include "cmul.mm"
include "co.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjdif.mm"
include "a1i.mm"
include "cun.mm"
include "wss.mm"
include "wcel.mm"
include "snssi.mm"
include "syl.mm"
include "undif.mm"
include "sylib.mm"
include "eqcomd.mm"
include "fprodsplitf.mm"
include "csb.mm"
include "cc.mm"
include "csbiedf.mm"
include "wa.mm"
include "ancli.mm"
include "cv.mm"
include "wi.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcsb1.mm"
include "nfel.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "prodsns.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "oveq1d.mm"

theorem fprodsplit1f
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume fprodsplit1f.kph: |- F/ k ph
  assume fprodsplit1f.fk: |- ( ph -> F/_ k D )
  assume fprodsplit1f.a: |- ( ph -> A e. Fin )
  assume fprodsplit1f.b: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fprodsplit1f.c: |- ( ph -> C e. A )
  assume fprodsplit1f.d: |- ( ( ph /\ k = C ) -> B = D )

  disjoint A k
  disjoint C k
  assert |- ( ph -> prod_ k e. A B = ( D x. prod_ k e. ( A \ { C } ) B ) )

  proof
    wph
    cA
    cB
    vk
    cprod
    cC
    csn
    #
    cB
    vk
    cprod
    #
    cA
    @0
    cdif
    #
    cB
    vk
    cprod
    #
    cmul
    co
    cD
    @3
    cmul
    co
    wph
    @0
    @2
    cB
    cA
    vk
    fprodsplit1f.kph
    @0
    @2
    cin
    c0
    wceq
    wph
    @0
    cA
    disjdif
    a1i
    wph
    @0
    @2
    cun
    #
    cA
    wph
    @0
    cA
    wss
    #
    @4
    cA
    wceq
    wph
    cC
    cA
    wcel
    #
    @5
    fprodsplit1f.c
    cC
    cA
    snssi
    syl
    @0
    cA
    undif
    sylib
    eqcomd
    fprodsplit1f.a
    fprodsplit1f.b
    fprodsplitf
    wph
    @1
    cD
    @3
    cmul
    wph
    @1
    vk
    cC
    cB
    csb
    #
    cD
    wph
    @6
    @7
    cc
    wcel
    #
    @1
    @7
    wceq
    fprodsplit1f.c
    wph
    @7
    cD
    cc
    wph
    vk
    cC
    cB
    cD
    cA
    fprodsplit1f.kph
    fprodsplit1f.fk
    fprodsplit1f.c
    fprodsplit1f.d
    csbiedf
    #
    wph
    cD
    @7
    cc
    wph
    @7
    cD
    @9
    eqcomd
    wph
    @6
    wph
    @6
    wa
    #
    @8
    fprodsplit1f.c
    wph
    @6
    fprodsplit1f.c
    ancli
    wph
    vk
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    cc
    wcel
    #
    wi
    @10
    @8
    wi
    vk
    cC
    cA
    vk
    cC
    nfcv
    #
    @10
    @8
    vk
    wph
    @6
    vk
    fprodsplit1f.kph
    @6
    vk
    nfv
    nfan
    vk
    @7
    cc
    vk
    cC
    cB
    @15
    nfcsb1
    vk
    cc
    nfcv
    nfel
    nfim
    @11
    cC
    wceq
    #
    @13
    @10
    @14
    @8
    @16
    @12
    @6
    wph
    @11
    cC
    cA
    eleq1
    anbi2d
    @16
    cB
    @7
    cc
    vk
    cC
    cB
    csbeq1a
    eleq1d
    imbi12d
    fprodsplit1f.b
    vtoclgf
    sylc
    eqeltrd
    eqeltrd
    cB
    vk
    cC
    cA
    prodsns
    syl2anc
    @9
    eqtrd
    oveq1d
    eqtrd
end
