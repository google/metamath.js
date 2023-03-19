include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cfz.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "elfzofz.mm"
include "elfzolt2.mm"
include "jca.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "elfzuz.mm"
include "adantr.mm"
include "elfzel2.mm"
include "simpr.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"
include "impbii.mm"

theorem elfzfzo
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( A e. ( M ..^ N ) <-> ( A e. ( M ... N ) /\ A < N ) )

  proof
    cA
    cM
    cN
    cfzo
    co
    wcel
    #
    cA
    cM
    cN
    cfz
    co
    wcel
    #
    cA
    cN
    clt
    wbr
    #
    wa
    #
    @0
    @1
    @2
    cA
    cM
    cN
    elfzofz
    cA
    cM
    cN
    elfzolt2
    jca
    @3
    cA
    cM
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    #
    @2
    @0
    @1
    @4
    @2
    cA
    cM
    cN
    elfzuz
    adantr
    @1
    @5
    @2
    cA
    cM
    cN
    elfzel2
    adantr
    @1
    @2
    simpr
    cA
    cM
    cN
    elfzo2
    syl3anbrc
    impbii
end
