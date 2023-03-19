include "wnf.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "w3a.mm"
include "wral.mm"
include "df-ral.mm"
include "wa.mm"
include "eleq1.mm"
include "pm5.32ri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "3bitr3i.mm"
include "albii.mm"
include "19.21v.mm"
include "3bitri.mm"
include "a1i.mm"
include "biimt.mm"
include "3ad2ant3.mm"
include "ceqsalt.mm"
include "3bitr2d.mm"

theorem ceqsralt
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) /\ A e. B ) -> ( A. x e. B ( x = A -> ph ) <-> ps ) )

  proof
    wps
    vx
    wnf
    #
    vx
    cv
    #
    cA
    wceq
    #
    wph
    wps
    wb
    wi
    vx
    wal
    #
    cA
    cB
    wcel
    #
    w3a
    #
    @2
    wph
    wi
    #
    vx
    cB
    wral
    #
    @4
    @6
    vx
    wal
    #
    wi
    #
    @8
    wps
    @7
    @9
    wb
    @5
    @7
    @1
    cB
    wcel
    #
    @6
    wi
    #
    vx
    wal
    @4
    @6
    wi
    #
    vx
    wal
    @9
    @6
    vx
    cB
    df-ral
    @11
    @12
    vx
    @10
    @2
    wa
    #
    wph
    wi
    @4
    @2
    wa
    #
    wph
    wi
    @11
    @12
    @13
    @14
    wph
    @2
    @10
    @4
    @1
    cA
    cB
    eleq1
    pm5.32ri
    imbi1i
    @10
    @2
    wph
    impexp
    @4
    @2
    wph
    impexp
    3bitr3i
    albii
    @4
    @6
    vx
    19.21v
    3bitri
    a1i
    @4
    @0
    @8
    @9
    wb
    @3
    @4
    @8
    biimt
    3ad2ant3
    wph
    wps
    vx
    cA
    cB
    ceqsalt
    3bitr2d
end
