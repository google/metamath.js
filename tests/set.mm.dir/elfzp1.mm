include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "wo.mm"
include "fzsuc.mm"
include "eleq2d.mm"
include "elun.mm"
include "ovex.mm"
include "elsn2.mm"
include "orbi2i.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem elfzp1
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( K e. ( M ... ( N + 1 ) ) <-> ( K e. ( M ... N ) \/ K = ( N + 1 ) ) ) )

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
    c1
    caddc
    co
    #
    cfz
    co
    #
    wcel
    cK
    cM
    cN
    cfz
    co
    #
    @1
    csn
    #
    cun
    #
    wcel
    #
    cK
    @3
    wcel
    #
    cK
    @1
    wceq
    #
    wo
    #
    @0
    @2
    @5
    cK
    cM
    cN
    fzsuc
    eleq2d
    @6
    @7
    cK
    @4
    wcel
    #
    wo
    @9
    cK
    @3
    @4
    elun
    @10
    @8
    @7
    cK
    @1
    cN
    c1
    caddc
    ovex
    elsn2
    orbi2i
    bitri
    syl6bb
end
