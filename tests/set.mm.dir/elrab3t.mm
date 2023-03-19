include "crab.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "cab.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "df-rab.mm"
include "eleq2i.mm"
include "id.mm"
include "nfa1.mm"
include "nfv.mm"
include "nfan.mm"
include "sp.mm"
include "eleq1.mm"
include "biimparc.mm"
include "biantrurd.mm"
include "bibi1d.mm"
include "pm5.74da.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "alrimi.mm"
include "elabgt.mm"
include "syl2an2.mm"
include "syl5bb.mm"

theorem elrab3t
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( ( A. x ( x = A -> ( ph <-> ps ) ) /\ A e. B ) -> ( A e. { x e. B | ph } <-> ps ) )

  proof
    cA
    wph
    vx
    cB
    crab
    #
    wcel
    cA
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    wcel
    #
    @1
    cA
    wceq
    #
    wph
    wps
    wb
    #
    wi
    #
    vx
    wal
    #
    cA
    cB
    wcel
    #
    wa
    #
    wps
    @0
    @4
    cA
    wph
    vx
    cB
    df-rab
    eleq2i
    @10
    @10
    @9
    @6
    @3
    wps
    wb
    #
    wi
    #
    vx
    wal
    @5
    wps
    wb
    @10
    id
    @11
    @13
    vx
    @9
    @10
    vx
    @8
    vx
    nfa1
    @10
    vx
    nfv
    nfan
    @9
    @10
    @13
    @9
    @8
    @10
    @13
    @8
    vx
    sp
    @10
    @6
    @7
    @12
    @10
    @6
    wa
    #
    wph
    @3
    wps
    @14
    @2
    wph
    @6
    @2
    @10
    @1
    cA
    cB
    eleq1
    biimparc
    biantrurd
    bibi1d
    pm5.74da
    syl5ibcom
    imp
    alrimi
    @3
    wps
    vx
    cA
    cB
    elabgt
    syl2an2
    syl5bb
end
