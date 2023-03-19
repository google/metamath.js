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
include "wa.mm"
include "cn.mm"
include "crab.mm"
include "cuz.mm"
include "cdioph.mm"
include "elnnuz.mm"
include "rabbii.mm"
include "1z.mm"
include "eluzrabdioph.mm"
include "mp3an2.mm"
include "syl5eqel.mm"

theorem elnnrabdioph
  let vt: setvar t
  let cA: class A
  let cN: class N
  let cM: class M

  disjoint N t
  disjoint M t
  assert |- ( ( N e. NN0 /\ ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. ( mzPoly ` ( 1 ... N ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | A e. NN } e. ( Dioph ` N ) )

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
    cA
    cmpt
    @1
    cmzp
    cfv
    wcel
    #
    wa
    cA
    cn
    wcel
    #
    vt
    cn0
    @1
    cmap
    co
    #
    crab
    cA
    c1
    cuz
    cfv
    wcel
    #
    vt
    @4
    crab
    #
    cN
    cdioph
    cfv
    #
    @3
    @5
    vt
    @4
    cA
    elnnuz
    rabbii
    @0
    c1
    cz
    wcel
    @2
    @6
    @7
    wcel
    1z
    vt
    cA
    c1
    cN
    eluzrabdioph
    mp3an2
    syl5eqel
end
