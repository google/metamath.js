include "wss.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "shlessi.mm"
include "shscomi.mm"
include "syl6sseq.mm"
include "shsidmi.mm"
include "sylan9ss.mm"
include "shsub1i.mm"
include "sstr.mm"
include "mpan.mm"
include "shsub2i.mm"
include "jca.mm"
include "impbii.mm"

theorem shslubi
  let cA: class A
  let cB: class B
  let cC: class C
  assume shslub.1: |- A e. SH
  assume shslub.2: |- B e. SH
  assume shslub.3: |- C e. SH


  assert |- ( ( A C_ C /\ B C_ C ) <-> ( A +H B ) C_ C )

  proof
    cA
    cC
    wss
    #
    cB
    cC
    wss
    #
    wa
    cA
    cB
    cph
    co
    #
    cC
    wss
    #
    @0
    @1
    @2
    cB
    cC
    cph
    co
    #
    cC
    @0
    @2
    cC
    cB
    cph
    co
    @4
    cA
    cC
    cB
    shslub.1
    shslub.3
    shslub.2
    shlessi
    cC
    cB
    shslub.3
    shslub.2
    shscomi
    syl6sseq
    @1
    @4
    cC
    cC
    cph
    co
    cC
    cB
    cC
    cC
    shslub.2
    shslub.3
    shslub.3
    shlessi
    cC
    shslub.3
    shsidmi
    syl6sseq
    sylan9ss
    @3
    @0
    @1
    cA
    @2
    wss
    @3
    @0
    cA
    cB
    shslub.1
    shslub.2
    shsub1i
    cA
    @2
    cC
    sstr
    mpan
    cB
    @2
    wss
    @3
    @1
    cB
    cA
    shslub.2
    shslub.1
    shsub2i
    cB
    @2
    cC
    sstr
    mpan
    jca
    impbii
end
