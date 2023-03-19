include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "wo.mm"
include "cvv.mm"
include "wa.mm"
include "elex.mm"
include "anim2i.mm"
include "elfvex.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "imdistani.mm"
include "jaodan.mm"
include "csn.mm"
include "cun.mm"
include "fzpred.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "elsng.mm"
include "orbi1d.mm"
include "sylan9bb.mm"
include "pm5.21nd.mm"

theorem elfzp12
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( K e. ( M ... N ) <-> ( K = M \/ K e. ( ( M + 1 ) ... N ) ) ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cK
    cM
    cN
    cfz
    co
    #
    wcel
    #
    cK
    cM
    wceq
    #
    cK
    cM
    c1
    caddc
    co
    cN
    cfz
    co
    #
    wcel
    #
    wo
    #
    @0
    cK
    cvv
    wcel
    #
    wa
    #
    @2
    @7
    @0
    cK
    @1
    elex
    anim2i
    @0
    @3
    @8
    @5
    @0
    @3
    @7
    @0
    @7
    @3
    cM
    cvv
    wcel
    cN
    cM
    cuz
    elfvex
    cK
    cM
    cvv
    eleq1
    syl5ibrcom
    imdistani
    @5
    @7
    @0
    cK
    @4
    elex
    anim2i
    jaodan
    @0
    @2
    cK
    cM
    csn
    #
    wcel
    #
    @5
    wo
    #
    @7
    @6
    @0
    @2
    cK
    @9
    @4
    cun
    #
    wcel
    @11
    @0
    @1
    @12
    cK
    cM
    cN
    fzpred
    eleq2d
    cK
    @9
    @4
    elun
    syl6bb
    @7
    @10
    @3
    @5
    cK
    cM
    cvv
    elsng
    orbi1d
    sylan9bb
    pm5.21nd
end
