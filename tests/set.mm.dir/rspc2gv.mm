include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "df-ral.mm"
include "imbi2i.mm"
include "albii.mm"
include "19.21v.mm"
include "bicomi.mm"
include "wceq.mm"
include "impexp.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "imbi12d.mm"
include "syl5bbr.mm"
include "spc2gv.mm"
include "pm2.43a.mm"
include "syl5bi.mm"

theorem rspc2gv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume rspc2gv.1: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint V x
  disjoint V y
  disjoint W x
  disjoint W y
  disjoint ps x
  disjoint ps y
  assert |- ( ( A e. V /\ B e. W ) -> ( A. x e. V A. y e. W ph -> ps ) )

  proof
    wph
    vy
    cW
    wral
    #
    vx
    cV
    wral
    vx
    cv
    #
    cV
    wcel
    #
    @0
    wi
    #
    vx
    wal
    #
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    wps
    @0
    vx
    cV
    df-ral
    @4
    @2
    vy
    cv
    #
    cW
    wcel
    #
    wph
    wi
    #
    vy
    wal
    #
    wi
    #
    vx
    wal
    #
    @7
    wps
    @3
    @12
    vx
    @0
    @11
    @2
    wph
    vy
    cW
    df-ral
    imbi2i
    albii
    @13
    @2
    @10
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    @7
    wps
    @12
    @15
    vx
    @15
    @12
    @2
    @10
    vy
    19.21v
    bicomi
    albii
    @16
    @7
    wps
    @14
    @7
    wps
    wi
    #
    vx
    vy
    cA
    cB
    cV
    cW
    @14
    @2
    @9
    wa
    #
    wph
    wi
    @1
    cA
    wceq
    #
    @8
    cB
    wceq
    #
    wa
    #
    @17
    @2
    @9
    wph
    impexp
    @21
    @18
    @7
    wph
    wps
    @19
    @2
    @5
    @20
    @9
    @6
    @1
    cA
    cV
    eleq1
    @8
    cB
    cW
    eleq1
    bi2anan9
    rspc2gv.1
    imbi12d
    syl5bbr
    spc2gv
    pm2.43a
    syl5bi
    syl5bi
    syl5bi
end
