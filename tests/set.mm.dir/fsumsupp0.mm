include "cc0.mm"
include "csupp.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "wfn.mm"
include "cfn.mm"
include "wcel.mm"
include "cr.mm"
include "wceq.mm"
include "cc.mm"
include "ffnd.mm"
include "0red.mm"
include "suppvalfn.mm"
include "syl3anc.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "cdif.mm"
include "wn.mm"
include "eldifi.mm"
include "neqne.mm"
include "adantl.mm"
include "jca.mm"
include "rabid.mm"
include "sylibr.mm"
include "adantll.mm"
include "wb.mm"
include "eleq2d.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "eldifn.mm"
include "ad2antlr.mm"
include "condan.mm"
include "fsumss.mm"

theorem fsumsupp0
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  assume fsumsupp0.a: |- ( ph -> A e. Fin )
  assume fsumsupp0.f: |- ( ph -> F : A --> CC )

  disjoint A k
  disjoint F k
  disjoint k ph
  assert |- ( ph -> sum_ k e. ( F supp 0 ) ( F ` k ) = sum_ k e. A ( F ` k ) )

  proof
    wph
    cF
    cc0
    csupp
    co
    #
    cA
    vk
    cv
    #
    cF
    cfv
    #
    vk
    wph
    @0
    @2
    cc0
    wne
    #
    vk
    cA
    crab
    #
    cA
    wph
    cF
    cA
    wfn
    cA
    cfn
    wcel
    cc0
    cr
    wcel
    @0
    @4
    wceq
    wph
    cA
    cc
    cF
    fsumsupp0.f
    ffnd
    fsumsupp0.a
    wph
    0red
    vk
    cF
    cfn
    cr
    cA
    cc0
    suppvalfn
    syl3anc
    #
    @3
    vk
    cA
    ssrab2
    syl6eqss
    #
    wph
    @1
    @0
    wcel
    #
    wa
    cA
    cc
    @1
    cF
    wph
    cA
    cc
    cF
    wf
    @7
    fsumsupp0.f
    adantr
    wph
    @0
    cA
    @1
    @6
    sselda
    ffvelrnd
    wph
    @1
    cA
    @0
    cdif
    wcel
    #
    wa
    #
    @2
    cc0
    wceq
    #
    @7
    @9
    @10
    wn
    #
    wa
    @7
    @1
    @4
    wcel
    #
    @8
    @11
    @12
    wph
    @8
    @11
    wa
    #
    @1
    cA
    wcel
    #
    @3
    wa
    @12
    @13
    @14
    @3
    @8
    @14
    @11
    @1
    cA
    @0
    eldifi
    adantr
    @11
    @3
    @8
    @2
    cc0
    neqne
    adantl
    jca
    @3
    vk
    cA
    rabid
    sylibr
    adantll
    wph
    @7
    @12
    wb
    @8
    @11
    wph
    @0
    @4
    @1
    @5
    eleq2d
    ad2antrr
    mpbird
    @8
    @7
    wn
    wph
    @11
    @1
    cA
    @0
    eldifn
    ad2antlr
    condan
    fsumsupp0.a
    fsumss
end
