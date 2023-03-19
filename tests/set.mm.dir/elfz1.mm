include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "w3a.mm"
include "fzval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "elrab.mm"
include "3anass.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem elfz1
  let cK: class K
  let cM: class M
  let cN: class N
  let vj: setvar j


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( K e. ( M ... N ) <-> ( K e. ZZ /\ M <_ K /\ K <_ N ) ) )

  proof
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    #
    cK
    cM
    cN
    cfz
    co
    #
    wcel
    cK
    cM
    vj
    cv
    #
    cle
    wbr
    #
    @2
    cN
    cle
    wbr
    #
    wa
    #
    vj
    cz
    crab
    #
    wcel
    #
    cK
    cz
    wcel
    #
    cM
    cK
    cle
    wbr
    #
    cK
    cN
    cle
    wbr
    #
    w3a
    #
    @0
    @1
    @6
    cK
    vj
    cM
    cN
    fzval
    eleq2d
    @7
    @8
    @9
    @10
    wa
    #
    wa
    @11
    @5
    @12
    vj
    cK
    cz
    @2
    cK
    wceq
    @3
    @9
    @4
    @10
    @2
    cK
    cM
    cle
    breq2
    @2
    cK
    cN
    cle
    breq1
    anbi12d
    elrab
    @8
    @9
    @10
    3anass
    bitr4i
    syl6bb
end
