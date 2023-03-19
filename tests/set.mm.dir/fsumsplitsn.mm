include "csn.mm"
include "cun.mm"
include "csu.mm"
include "caddc.mm"
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
include "simpll.mm"
include "elunnel1.mm"
include "elsni.mm"
include "syl.mm"
include "adantll.mm"
include "adantl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "pm2.61dan.mm"
include "fsumsplitf.mm"
include "sumsnf.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem fsumsplitsn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cV: class V
  assume fsumsplitsn.ph: |- F/ k ph
  assume fsumsplitsn.kd: |- F/_ k D
  assume fsumsplitsn.a: |- ( ph -> A e. Fin )
  assume fsumsplitsn.b: |- ( ph -> B e. V )
  assume fsumsplitsn.ba: |- ( ph -> -. B e. A )
  assume fsumsplitsn.c: |- ( ( ph /\ k e. A ) -> C e. CC )
  assume fsumsplitsn.d: |- ( k = B -> C = D )
  assume fsumsplitsn.dcn: |- ( ph -> D e. CC )

  disjoint A k
  disjoint B k
  disjoint V k
  assert |- ( ph -> sum_ k e. ( A u. { B } ) C = ( sum_ k e. A C + D ) )

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
    csu
    cA
    cC
    vk
    csu
    #
    @0
    cC
    vk
    csu
    #
    caddc
    co
    @2
    cD
    caddc
    co
    wph
    cA
    @0
    cC
    @1
    vk
    fsumsplitsn.ph
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
    fsumsplitsn.ba
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
    fsumsplitsn.a
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
    fsumsplitsn.c
    adantlr
    @7
    @8
    wn
    #
    wa
    wph
    @5
    cB
    wceq
    #
    @9
    wph
    @6
    @10
    simpll
    @6
    @10
    @11
    wph
    @6
    @10
    wa
    @5
    @0
    wcel
    @11
    @5
    cA
    @0
    elunnel1
    @5
    cB
    elsni
    syl
    adantll
    wph
    @11
    wa
    cC
    cD
    cc
    @11
    cC
    cD
    wceq
    wph
    fsumsplitsn.d
    adantl
    wph
    cD
    cc
    wcel
    #
    @11
    fsumsplitsn.dcn
    adantr
    eqeltrd
    syl2anc
    pm2.61dan
    fsumsplitf
    wph
    @3
    cD
    @2
    caddc
    wph
    cB
    cV
    wcel
    @12
    @3
    cD
    wceq
    fsumsplitsn.b
    fsumsplitsn.dcn
    cC
    cD
    vk
    cB
    cV
    fsumsplitsn.kd
    fsumsplitsn.d
    sumsnf
    syl2anc
    oveq2d
    eqtrd
end
