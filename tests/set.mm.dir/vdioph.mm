include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "cc0.mm"
include "wceq.mm"
include "crab.mm"
include "cdioph.mm"
include "cfv.mm"
include "wral.mm"
include "eqid.mm"
include "rgenw.mm"
include "rabid2.mm"
include "mpbir.mm"
include "cz.mm"
include "cmpt.mm"
include "cmzp.mm"
include "cvv.mm"
include "ovex.mm"
include "0z.mm"
include "mzpconstmpt.mm"
include "mp2an.mm"
include "eq0rabdioph.mm"
include "mpan2.mm"
include "syl5eqel.mm"

theorem vdioph
  let cA: class A
  let cN: class N
  let vt: setvar t
  let va: setvar a
  let vb: setvar b
  let cB: class B


  assert |- ( A e. NN0 -> ( NN0 ^m ( 1 ... A ) ) e. ( Dioph ` A ) )

  proof
    cA
    cn0
    wcel
    #
    cn0
    c1
    cA
    cfz
    co
    #
    cmap
    co
    #
    cc0
    cc0
    wceq
    #
    va
    @2
    crab
    #
    cA
    cdioph
    cfv
    #
    @2
    @4
    wceq
    @3
    va
    @2
    wral
    @3
    va
    @2
    cc0
    eqid
    rgenw
    @3
    va
    @2
    rabid2
    mpbir
    @0
    va
    cz
    @1
    cmap
    co
    cc0
    cmpt
    @1
    cmzp
    cfv
    wcel
    #
    @4
    @5
    wcel
    @1
    cvv
    wcel
    cc0
    cz
    wcel
    @6
    c1
    cA
    cfz
    ovex
    0z
    va
    cc0
    @1
    mzpconstmpt
    mp2an
    va
    cc0
    cA
    eq0rabdioph
    mpan2
    syl5eqel
end
