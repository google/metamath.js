include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "cfg.mm"
include "co.mm"
include "wb.mm"
include "ibar.mm"
include "adantl.mm"
include "cfbas.mm"
include "filfbas.mm"
include "elfg.mm"
include "syl.mm"
include "adantr.mm"
include "fgfil.mm"
include "eleq2d.mm"
include "3bitr2rd.mm"

theorem elfilss
  let vt: setvar t
  let cA: class A
  let cF: class F
  let cX: class X
  let vx: setvar x

  disjoint F t
  disjoint X t
  disjoint A t
  disjoint t x
  disjoint F x
  disjoint X x
  assert |- ( ( F e. ( Fil ` X ) /\ A C_ X ) -> ( A e. F <-> E. t e. F t C_ A ) )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    #
    cA
    cX
    wss
    #
    wa
    vt
    cv
    cA
    wss
    vt
    cF
    wrex
    #
    @1
    @2
    wa
    #
    cA
    cX
    cF
    cfg
    co
    #
    wcel
    #
    cA
    cF
    wcel
    #
    @1
    @2
    @3
    wb
    @0
    @1
    @2
    ibar
    adantl
    @0
    @5
    @3
    wb
    #
    @1
    @0
    cF
    cX
    cfbas
    cfv
    wcel
    @7
    cF
    cX
    filfbas
    vt
    cA
    cF
    cX
    elfg
    syl
    adantr
    @0
    @5
    @6
    wb
    @1
    @0
    @4
    cF
    cA
    cF
    cX
    fgfil
    eleq2d
    adantr
    3bitr2rd
end
