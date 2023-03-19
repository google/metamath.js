include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "ccda.mm"
include "co.mm"
include "csdm.mm"
include "wbr.mm"
include "wo.mm"
include "wne.mm"
include "wn.mm"
include "cen.mm"
include "cfin5.mm"
include "wa.mm"
include "wb.mm"
include "nne.mm"
include "bicomi.mm"
include "a1i.mm"
include "cdom.mm"
include "cdadom3.mm"
include "anidms.mm"
include "brsdom.mm"
include "baib.mm"
include "syl.mm"
include "orbi12d.mm"
include "isfin5.mm"
include "ianor.mm"
include "3bitr4g.mm"

theorem isfin5-2
  let cA: class A
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A e. V -> ( A e. Fin5 <-> -. ( A =/= (/) /\ A ~~ ( A +c A ) ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    c0
    wceq
    #
    cA
    cA
    cA
    ccda
    co
    #
    csdm
    wbr
    #
    wo
    cA
    c0
    wne
    #
    wn
    #
    cA
    @2
    cen
    wbr
    #
    wn
    #
    wo
    cA
    cfin5
    wcel
    @4
    @6
    wa
    wn
    @0
    @1
    @5
    @3
    @7
    @1
    @5
    wb
    @0
    @5
    @1
    cA
    c0
    nne
    bicomi
    a1i
    @0
    cA
    @2
    cdom
    wbr
    #
    @3
    @7
    wb
    @0
    @8
    cA
    cA
    cV
    cV
    cdadom3
    anidms
    @3
    @8
    @7
    cA
    @2
    brsdom
    baib
    syl
    orbi12d
    cA
    isfin5
    @4
    @6
    ianor
    3bitr4g
end
