include "cn0.mm"
include "wcel.mm"
include "c0.mm"
include "c1.mm"
include "cc0.mm"
include "wceq.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "crab.mm"
include "cdioph.mm"
include "cfv.mm"
include "wn.mm"
include "wral.mm"
include "ax-1ne0.mm"
include "neii.mm"
include "rgenw.mm"
include "rabeq0.mm"
include "mpbir.mm"
include "cz.mm"
include "cmpt.mm"
include "cmzp.mm"
include "cvv.mm"
include "ovex.mm"
include "1z.mm"
include "mzpconstmpt.mm"
include "mp2an.mm"
include "eq0rabdioph.mm"
include "mpan2.mm"
include "syl5eqelr.mm"

theorem 0dioph
  let cA: class A
  let cN: class N
  let vt: setvar t
  let va: setvar a
  let vb: setvar b
  let cB: class B


  assert |- ( A e. NN0 -> (/) e. ( Dioph ` A ) )

  proof
    cA
    cn0
    wcel
    #
    c0
    c1
    cc0
    wceq
    #
    va
    cn0
    c1
    cA
    cfz
    co
    #
    cmap
    co
    #
    crab
    #
    cA
    cdioph
    cfv
    #
    @4
    c0
    wceq
    @1
    wn
    #
    va
    @3
    wral
    @6
    va
    @3
    c1
    cc0
    ax-1ne0
    neii
    rgenw
    @1
    va
    @3
    rabeq0
    mpbir
    @0
    va
    cz
    @2
    cmap
    co
    c1
    cmpt
    @2
    cmzp
    cfv
    wcel
    #
    @4
    @5
    wcel
    @2
    cvv
    wcel
    c1
    cz
    wcel
    @7
    c1
    cA
    cfz
    ovex
    1z
    va
    c1
    @2
    mzpconstmpt
    mp2an
    va
    c1
    cA
    eq0rabdioph
    mpan2
    syl5eqelr
end
