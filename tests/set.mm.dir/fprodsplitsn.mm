include "csn.mm"
include "cun.mm"
include "cprod.mm"
include "cmul.mm"
include "co.mm"
include "wcel.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjsn.mm"
include "sylibr.mm"
include "eqidd.mm"
include "cfn.mm"
include "snfi.mm"
include "a1i.mm"
include "unfi.mm"
include "syl2anc.mm"
include "cv.mm"
include "wa.mm"
include "cc.mm"
include "adantlr.mm"
include "elunnel1.mm"
include "elsni.mm"
include "syl.mm"
include "adantll.mm"
include "simpll.mm"
include "eqeltrd.mm"
include "pm2.61dan.mm"
include "fprodsplitf.mm"
include "prodsnf.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem fprodsplitsn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cV: class V
  assume fprodsplitsn.ph: |- F/ k ph
  assume fprodsplitsn.kd: |- F/_ k D
  assume fprodsplitsn.a: |- ( ph -> A e. Fin )
  assume fprodsplitsn.b: |- ( ph -> B e. V )
  assume fprodsplitsn.ba: |- ( ph -> -. B e. A )
  assume fprodsplitsn.c: |- ( ( ph /\ k e. A ) -> C e. CC )
  assume fprodsplitsn.d: |- ( k = B -> C = D )
  assume fprodsplitsn.dcn: |- ( ph -> D e. CC )

  disjoint A k
  disjoint B k
  disjoint V k
  assert |- ( ph -> prod_ k e. ( A u. { B } ) C = ( prod_ k e. A C x. D ) )

  proof
    wph
    cA
    cB
    csn
    #
    cun
    #
    cC
    vk
    cprod
    cA
    cC
    vk
    cprod
    #
    @0
    cC
    vk
    cprod
    #
    cmul
    co
    @2
    cD
    cmul
    co
    wph
    cA
    @0
    cC
    @1
    vk
    fprodsplitsn.ph
    wph
    cB
    cA
    wcel
    wn
    cA
    @0
    cin
    c0
    wceq
    fprodsplitsn.ba
    cA
    cB
    disjsn
    sylibr
    wph
    @1
    eqidd
    wph
    cA
    cfn
    wcel
    @0
    cfn
    wcel
    #
    @1
    cfn
    wcel
    fprodsplitsn.a
    @4
    wph
    cB
    snfi
    a1i
    cA
    @0
    unfi
    syl2anc
    wph
    vk
    cv
    #
    @1
    wcel
    #
    wa
    #
    @5
    cA
    wcel
    #
    cC
    cc
    wcel
    #
    wph
    @8
    @9
    @6
    fprodsplitsn.c
    adantlr
    @7
    @8
    wn
    #
    wa
    #
    cC
    cD
    cc
    @11
    @5
    cB
    wceq
    #
    cC
    cD
    wceq
    @6
    @10
    @12
    wph
    @6
    @10
    wa
    @5
    @0
    wcel
    @12
    @5
    cA
    @0
    elunnel1
    @5
    cB
    elsni
    syl
    adantll
    fprodsplitsn.d
    syl
    @11
    wph
    cD
    cc
    wcel
    #
    wph
    @6
    @10
    simpll
    fprodsplitsn.dcn
    syl
    eqeltrd
    pm2.61dan
    fprodsplitf
    wph
    @3
    cD
    @2
    cmul
    wph
    cB
    cV
    wcel
    @13
    @3
    cD
    wceq
    fprodsplitsn.b
    fprodsplitsn.dcn
    cC
    cD
    vk
    cB
    cV
    fprodsplitsn.kd
    fprodsplitsn.d
    prodsnf
    syl2anc
    oveq2d
    eqtrd
end
