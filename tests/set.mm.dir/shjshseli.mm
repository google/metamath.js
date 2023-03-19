include "cph.mm"
include "co.mm"
include "cch.mm"
include "wcel.mm"
include "chj.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "shjshsi.mm"
include "ococ.mm"
include "syl5req.mm"
include "shjcli.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem shjshseli
  let cA: class A
  let cB: class B
  assume shjshs.1: |- A e. SH
  assume shjshs.2: |- B e. SH


  assert |- ( ( A +H B ) e. CH <-> ( A +H B ) = ( A vH B ) )

  proof
    cA
    cB
    cph
    co
    #
    cch
    wcel
    #
    @0
    cA
    cB
    chj
    co
    #
    wceq
    #
    @1
    @2
    @0
    cort
    cfv
    cort
    cfv
    @0
    cA
    cB
    shjshs.1
    shjshs.2
    shjshsi
    @0
    ococ
    syl5req
    @3
    @1
    @2
    cch
    wcel
    cA
    cB
    shjshs.1
    shjshs.2
    shjcli
    @0
    @2
    cch
    eleq1
    mpbiri
    impbii
end
