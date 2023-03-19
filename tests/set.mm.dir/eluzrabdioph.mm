include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "cmpt.mm"
include "cmzp.mm"
include "cfv.mm"
include "w3a.mm"
include "cuz.mm"
include "crab.mm"
include "cle.mm"
include "wbr.mm"
include "cdioph.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "wral.mm"
include "rabdiophlem1.mm"
include "eluz.mm"
include "ex.mm"
include "ralimdv.mm"
include "imp.mm"
include "sylan2.mm"
include "rabbi.mm"
include "sylib.mm"
include "3adant1.mm"
include "cvv.mm"
include "ovex.mm"
include "mzpconstmpt.mm"
include "mpan.mm"
include "lerabdioph.mm"
include "syl3an2.mm"
include "eqeltrd.mm"

theorem eluzrabdioph
  let vt: setvar t
  let cA: class A
  let cM: class M
  let cN: class N

  disjoint N t
  disjoint M t
  assert |- ( ( N e. NN0 /\ M e. ZZ /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A e. ( ZZ>= ` M ) } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    cM
    cz
    wcel
    #
    vt
    cz
    c1
    cN
    cfz
    co
    #
    cmap
    co
    #
    cA
    cmpt
    @2
    cmzp
    cfv
    #
    wcel
    #
    w3a
    cA
    cM
    cuz
    cfv
    wcel
    #
    vt
    cn0
    @2
    cmap
    co
    #
    crab
    #
    cM
    cA
    cle
    wbr
    #
    vt
    @7
    crab
    #
    cN
    cdioph
    cfv
    #
    @1
    @5
    @8
    @10
    wceq
    #
    @0
    @1
    @5
    wa
    @6
    @9
    wb
    #
    vt
    @7
    wral
    #
    @12
    @5
    @1
    cA
    cz
    wcel
    #
    vt
    @7
    wral
    #
    @14
    vt
    cA
    cN
    rabdiophlem1
    @1
    @16
    @14
    @1
    @15
    @13
    vt
    @7
    @1
    @15
    @13
    cM
    cA
    eluz
    ex
    ralimdv
    imp
    sylan2
    @6
    @9
    vt
    @7
    rabbi
    sylib
    3adant1
    @1
    @0
    vt
    @3
    cM
    cmpt
    @4
    wcel
    #
    @5
    @10
    @11
    wcel
    @2
    cvv
    wcel
    @1
    @17
    c1
    cN
    cfz
    ovex
    vt
    cM
    @2
    mzpconstmpt
    mpan
    vt
    cM
    cA
    cN
    lerabdioph
    syl3an2
    eqeltrd
end
