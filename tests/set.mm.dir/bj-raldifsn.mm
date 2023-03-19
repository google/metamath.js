include "wcel.mm"
include "wral.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "wa.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "raleqdv.mm"
include "wb.mm"
include "ralunb.mm"
include "a1i.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "wceq.mm"
include "velsn.mm"
include "imbi1i.mm"
include "albii.mm"
include "nfv.mm"
include "bj-ceqsalgv.mm"
include "syl5bb.mm"
include "anbi2d.mm"
include "3bitrd.mm"

theorem bj-raldifsn
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume bj-raldifsn.es: |- ( x = B -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( B e. A -> ( A. x e. A ph <-> ( A. x e. ( A \ { B } ) ph /\ ps ) ) )

  proof
    cB
    cA
    wcel
    #
    wph
    vx
    cA
    wral
    wph
    vx
    cA
    cB
    csn
    #
    cdif
    #
    @1
    cun
    #
    wral
    #
    wph
    vx
    @2
    wral
    #
    wph
    vx
    @1
    wral
    #
    wa
    #
    @5
    wps
    wa
    @0
    wph
    vx
    cA
    @3
    @0
    @3
    cA
    cA
    cB
    difsnid
    eqcomd
    raleqdv
    @4
    @7
    wb
    @0
    wph
    vx
    @2
    @1
    ralunb
    a1i
    @0
    @6
    wps
    @5
    @6
    vx
    cv
    #
    @1
    wcel
    #
    wph
    wi
    #
    vx
    wal
    #
    @0
    wps
    wph
    vx
    @1
    df-ral
    @11
    @8
    cB
    wceq
    #
    wph
    wi
    #
    vx
    wal
    @0
    wps
    @10
    @13
    vx
    @9
    @12
    wph
    vx
    cB
    velsn
    imbi1i
    albii
    wph
    wps
    vx
    cB
    cA
    wps
    vx
    nfv
    bj-raldifsn.es
    bj-ceqsalgv
    syl5bb
    syl5bb
    anbi2d
    3bitrd
end
