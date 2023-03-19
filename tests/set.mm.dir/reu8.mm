include "wreu.mm"
include "weq.mm"
include "wb.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "cbvreuv.mm"
include "reu6.mm"
include "cv.mm"
include "wcel.mm"
include "dfbi2.mm"
include "ralbii.mm"
include "ancom.mm"
include "equcom.mm"
include "imbi2i.mm"
include "a1i.mm"
include "biimt.mm"
include "wal.mm"
include "df-ral.mm"
include "bi2.04.mm"
include "albii.mm"
include "eleq1w.mm"
include "imbi12d.mm"
include "bicomd.mm"
include "equcoms.mm"
include "equsalvw.mm"
include "3bitrri.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "r19.26.mm"
include "syl6rbbr.mm"
include "rexbiia.mm"
include "3bitri.mm"

theorem reu8
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume rmo4.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint ps x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint ph z
  disjoint ps z
  assert |- ( E! x e. A ph <-> E. x e. A ( ph /\ A. y e. A ( ps -> x = y ) ) )

  proof
    wph
    vx
    cA
    wreu
    wps
    vy
    cA
    wreu
    wps
    vy
    vx
    weq
    #
    wb
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    wph
    wps
    vx
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    wrex
    wph
    wps
    vx
    vy
    cA
    rmo4.1
    cbvreuv
    wps
    vy
    vx
    cA
    reu6
    @2
    @6
    vx
    cA
    @2
    wps
    @0
    wi
    #
    @0
    wps
    wi
    #
    wa
    #
    vy
    cA
    wral
    #
    vx
    cv
    cA
    wcel
    #
    @6
    @1
    @9
    vy
    cA
    wps
    @0
    dfbi2
    ralbii
    @11
    @6
    @7
    vy
    cA
    wral
    #
    @8
    vy
    cA
    wral
    #
    wa
    #
    @10
    @6
    @5
    wph
    wa
    @11
    @14
    wph
    @5
    ancom
    @11
    @5
    @12
    wph
    @13
    @5
    @12
    wb
    @11
    @4
    @7
    vy
    cA
    @3
    @0
    wps
    vx
    vy
    equcom
    imbi2i
    ralbii
    a1i
    @11
    wph
    @11
    wph
    wi
    #
    @13
    @11
    wph
    biimt
    @13
    vy
    cv
    cA
    wcel
    #
    @8
    wi
    #
    vy
    wal
    @0
    @16
    wps
    wi
    #
    wi
    #
    vy
    wal
    @15
    @8
    vy
    cA
    df-ral
    @17
    @19
    vy
    @16
    @0
    wps
    bi2.04
    albii
    @18
    @15
    vy
    vx
    @18
    @15
    wb
    vx
    vy
    @3
    @15
    @18
    @3
    @11
    @16
    wph
    wps
    vx
    vy
    cA
    eleq1w
    rmo4.1
    imbi12d
    bicomd
    equcoms
    equsalvw
    3bitrri
    syl6bb
    anbi12d
    syl5bb
    @7
    @8
    vy
    cA
    r19.26
    syl6rbbr
    syl5bb
    rexbiia
    3bitri
end
