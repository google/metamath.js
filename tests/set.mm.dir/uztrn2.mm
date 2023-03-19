include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "eleq2i.mm"
include "uztrn.mm"
include "ancoms.mm"
include "sylanb.mm"
include "syl6eleqr.mm"

theorem uztrn2
  let cK: class K
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume uztrn2.1: |- Z = ( ZZ>= ` K )


  assert |- ( ( N e. Z /\ M e. ( ZZ>= ` N ) ) -> M e. Z )

  proof
    cN
    cZ
    wcel
    #
    cM
    cN
    cuz
    cfv
    wcel
    #
    wa
    cM
    cK
    cuz
    cfv
    #
    cZ
    @0
    cN
    @2
    wcel
    #
    @1
    cM
    @2
    wcel
    #
    cZ
    @2
    cN
    uztrn2.1
    eleq2i
    @1
    @3
    @4
    cN
    cM
    cK
    uztrn
    ancoms
    sylanb
    uztrn2.1
    syl6eleqr
end
