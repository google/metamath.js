include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "cabs.mm"
include "ccom.mm"
include "clo1.mm"
include "cfv.mm"
include "cc.mm"
include "wf.mm"
include "wb.mm"
include "eqid.mm"
include "fmptd.mm"
include "lo1o1.mm"
include "syl.mm"
include "cv.mm"
include "eqidd.mm"
include "cr.mm"
include "absf.mm"
include "a1i.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "eleq1d.mm"
include "bitrd.mm"

theorem lo1o12
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume lo1o12.1: |- ( ( ph /\ x e. A ) -> B e. CC )

  disjoint A x
  disjoint ph x
  disjoint x y
  disjoint B y
  assert |- ( ph -> ( ( x e. A |-> B ) e. O(1) <-> ( x e. A |-> ( abs ` B ) ) e. <_O(1) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    co1
    wcel
    #
    cabs
    @0
    ccom
    #
    clo1
    wcel
    #
    vx
    cA
    cB
    cabs
    cfv
    #
    cmpt
    #
    clo1
    wcel
    wph
    cA
    cc
    @0
    wf
    @1
    @3
    wb
    wph
    vx
    cA
    cB
    cc
    @0
    lo1o12.1
    @0
    eqid
    fmptd
    cA
    @0
    lo1o1
    syl
    wph
    @2
    @5
    clo1
    wph
    vx
    vy
    cA
    cc
    cB
    vy
    cv
    #
    cabs
    cfv
    @4
    @0
    cabs
    lo1o12.1
    wph
    @0
    eqidd
    wph
    vy
    cc
    cr
    cabs
    cc
    cr
    cabs
    wf
    wph
    absf
    a1i
    feqmptd
    @6
    cB
    cabs
    fveq2
    fmptco
    eleq1d
    bitrd
end
