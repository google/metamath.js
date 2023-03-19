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
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cmin.mm"
include "cdioph.mm"
include "wceq.mm"
include "wral.mm"
include "rabdiophlem1.mm"
include "wa.mm"
include "wb.mm"
include "znn0sub.mm"
include "ralimi.mm"
include "r19.26.mm"
include "rabbi.mm"
include "3imtr3i.mm"
include "syl2an.mm"
include "3adant1.mm"
include "simp1.mm"
include "mzpsubmpt.mm"
include "ancoms.mm"
include "elnn0rabdioph.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem lerabdioph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cN: class N
  let cM: class M

  disjoint N t
  disjoint M t
  assert |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. ( mzPoly ` ( 1 ... N ) ) /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> B ) e. ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A <_ B } e. ( Dioph ` N ) )

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
    cle
    wbr
    #
    vt
    cn0
    @1
    cmap
    co
    #
    crab
    #
    cB
    cA
    cmin
    co
    #
    cn0
    wcel
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
    @12
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
    @14
    @5
    vt
    cA
    cN
    rabdiophlem1
    vt
    cB
    cN
    rabdiophlem1
    @15
    @17
    wa
    #
    vt
    @8
    wral
    @7
    @11
    wb
    #
    vt
    @8
    wral
    @16
    @18
    wa
    @14
    @19
    @20
    vt
    @8
    cA
    cB
    znn0sub
    ralimi
    @15
    @17
    vt
    @8
    r19.26
    @7
    @11
    vt
    @8
    rabbi
    3imtr3i
    syl2an
    3adant1
    @6
    @0
    vt
    @2
    @10
    cmpt
    @3
    wcel
    #
    @12
    @13
    wcel
    @0
    @4
    @5
    simp1
    @4
    @5
    @21
    @0
    @5
    @4
    @21
    vt
    cB
    cA
    @1
    mzpsubmpt
    ancoms
    3adant1
    vt
    @10
    cN
    elnn0rabdioph
    syl2anc
    eqeltrd
end
