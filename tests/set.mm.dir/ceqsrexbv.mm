include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "r19.42v.mm"
include "wb.mm"
include "eleq1.mm"
include "adantr.mm"
include "pm5.32ri.mm"
include "bicomi.mm"
include "baib.mm"
include "rexbiia.mm"
include "ceqsrexv.mm"
include "pm5.32i.mm"
include "3bitr3i.mm"

theorem ceqsrexbv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ceqsrexv.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( E. x e. B ( x = A /\ ph ) <-> ( A e. B /\ ps ) )

  proof
    cA
    cB
    wcel
    #
    vx
    cv
    #
    cA
    wceq
    #
    wph
    wa
    #
    wa
    #
    vx
    cB
    wrex
    @0
    @3
    vx
    cB
    wrex
    #
    wa
    @5
    @0
    wps
    wa
    @0
    @3
    vx
    cB
    r19.42v
    @4
    @3
    vx
    cB
    @4
    @1
    cB
    wcel
    #
    @3
    @6
    @3
    wa
    @4
    @3
    @6
    @0
    @2
    @6
    @0
    wb
    wph
    @1
    cA
    cB
    eleq1
    adantr
    pm5.32ri
    bicomi
    baib
    rexbiia
    @0
    @5
    wps
    wph
    wps
    vx
    cA
    cB
    ceqsrexv.1
    ceqsrexv
    pm5.32i
    3bitr3i
end
