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
include "wne.mm"
include "crab.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cdioph.mm"
include "wceq.mm"
include "wral.mm"
include "rabdiophlem1.mm"
include "wa.mm"
include "wb.mm"
include "cr.mm"
include "zre.mm"
include "lttri2.mm"
include "syl2an.mm"
include "ralimi.mm"
include "r19.26.mm"
include "rabbi.mm"
include "3imtr3i.mm"
include "3adant1.mm"
include "ltrabdioph.mm"
include "3com23.mm"
include "orrabdioph.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem nerabdioph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cN: class N
  let cM: class M

  disjoint N t
  disjoint M t
  assert |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. ( mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A =/= B } e. ( Dioph ` N ) )

  proof
    cN
    cn0
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
    @1
    cmzp
    cfv
    #
    wcel
    #
    vt
    @2
    cB
    cmpt
    @3
    wcel
    #
    w3a
    #
    cA
    cB
    wne
    #
    vt
    cn0
    @1
    cmap
    co
    #
    crab
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    clt
    wbr
    #
    wo
    #
    vt
    @8
    crab
    #
    cN
    cdioph
    cfv
    #
    @4
    @5
    @9
    @13
    wceq
    #
    @0
    @4
    cA
    cz
    wcel
    #
    vt
    @8
    wral
    #
    cB
    cz
    wcel
    #
    vt
    @8
    wral
    #
    @15
    @5
    vt
    cA
    cN
    rabdiophlem1
    vt
    cB
    cN
    rabdiophlem1
    @16
    @18
    wa
    #
    vt
    @8
    wral
    @7
    @12
    wb
    #
    vt
    @8
    wral
    @17
    @19
    wa
    @15
    @20
    @21
    vt
    @8
    @16
    cA
    cr
    wcel
    cB
    cr
    wcel
    @21
    @18
    cA
    zre
    cB
    zre
    cA
    cB
    lttri2
    syl2an
    ralimi
    @16
    @18
    vt
    @8
    r19.26
    @7
    @12
    vt
    @8
    rabbi
    3imtr3i
    syl2an
    3adant1
    @6
    @10
    vt
    @8
    crab
    @14
    wcel
    @11
    vt
    @8
    crab
    @14
    wcel
    #
    @13
    @14
    wcel
    vt
    cA
    cB
    cN
    ltrabdioph
    @0
    @5
    @4
    @22
    vt
    cB
    cA
    cN
    ltrabdioph
    3com23
    @10
    @11
    vt
    cN
    orrabdioph
    syl2anc
    eqeltrd
end
