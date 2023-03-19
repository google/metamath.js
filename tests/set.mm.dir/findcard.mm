include "cfn.mm"
include "cv.mm"
include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "isfi.mm"
include "wi.mm"
include "wal.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi1d.mm"
include "albidv.mm"
include "en0.mm"
include "mpbiri.mm"
include "sylbi.mm"
include "ax-gen.mm"
include "w3a.mm"
include "wral.mm"
include "wa.mm"
include "peano2.mm"
include "rspcev.mm"
include "sylan.mm"
include "sylibr.mm"
include "3adant2.mm"
include "csn.mm"
include "cdif.mm"
include "dif1en.mm"
include "3expa.mm"
include "cvv.mm"
include "vex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "breq1.mm"
include "imbi12d.mm"
include "spcv.mm"
include "syl5com.mm"
include "ralrimdva.mm"
include "imp.mm"
include "an32s.mm"
include "3impa.mm"
include "sylc.mm"
include "3exp.mm"
include "alrimdv.mm"
include "cbvalv.mm"
include "syl6ibr.mm"
include "finds1.mm"
include "19.21bi.mm"
include "rexlimiv.mm"
include "vtoclga.mm"

theorem findcard
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vv: setvar v
  let vw: setvar w
  assume findcard.1: |- ( x = (/) -> ( ph <-> ps ) )
  assume findcard.2: |- ( x = ( y \ { z } ) -> ( ph <-> ch ) )
  assume findcard.3: |- ( x = y -> ( ph <-> th ) )
  assume findcard.4: |- ( x = A -> ( ph <-> ta ) )
  assume findcard.5: |- ps
  assume findcard.6: |- ( y e. Fin -> ( A. z e. y ch -> th ) )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint ph y
  disjoint ph z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph v
  disjoint ph w
  assert |- ( A e. Fin -> ta )

  proof
    wph
    wta
    vx
    cA
    cfn
    findcard.4
    vx
    cv
    #
    cfn
    wcel
    @0
    vw
    cv
    #
    cen
    wbr
    #
    vw
    com
    wrex
    wph
    vw
    @0
    isfi
    @2
    wph
    vw
    com
    @1
    com
    wcel
    @2
    wph
    wi
    #
    vx
    @3
    vx
    wal
    @0
    c0
    cen
    wbr
    #
    wph
    wi
    #
    vx
    wal
    @0
    vv
    cv
    #
    cen
    wbr
    #
    wph
    wi
    #
    vx
    wal
    #
    @0
    @6
    csuc
    #
    cen
    wbr
    #
    wph
    wi
    #
    vx
    wal
    #
    vw
    vv
    @1
    c0
    wceq
    #
    @3
    @5
    vx
    @14
    @2
    @4
    wph
    @1
    c0
    @0
    cen
    breq2
    imbi1d
    albidv
    @1
    @6
    wceq
    #
    @3
    @8
    vx
    @15
    @2
    @7
    wph
    @1
    @6
    @0
    cen
    breq2
    imbi1d
    albidv
    @1
    @10
    wceq
    #
    @3
    @12
    vx
    @16
    @2
    @11
    wph
    @1
    @10
    @0
    cen
    breq2
    imbi1d
    albidv
    @5
    vx
    @4
    @0
    c0
    wceq
    #
    wph
    @0
    en0
    @17
    wph
    wps
    findcard.5
    findcard.1
    mpbiri
    sylbi
    ax-gen
    @6
    com
    wcel
    #
    @9
    vy
    cv
    #
    @10
    cen
    wbr
    #
    wth
    wi
    #
    vy
    wal
    @13
    @18
    @9
    @21
    vy
    @18
    @9
    @20
    wth
    @18
    @9
    @20
    w3a
    @19
    cfn
    wcel
    #
    wch
    vz
    @19
    wral
    #
    wth
    @18
    @20
    @22
    @9
    @18
    @20
    wa
    #
    @19
    @1
    cen
    wbr
    #
    vw
    com
    wrex
    #
    @22
    @18
    @10
    com
    wcel
    @20
    @26
    @6
    peano2
    @25
    @20
    vw
    @10
    com
    @1
    @10
    @19
    cen
    breq2
    rspcev
    sylan
    vw
    @19
    isfi
    sylibr
    3adant2
    @18
    @9
    @20
    @23
    @18
    @20
    @9
    @23
    @24
    @9
    @23
    @24
    @9
    wch
    vz
    @19
    @24
    vz
    cv
    #
    @19
    wcel
    #
    wa
    @19
    @27
    csn
    #
    cdif
    #
    @6
    cen
    wbr
    #
    @9
    wch
    @18
    @20
    @28
    @31
    @19
    @6
    @27
    dif1en
    3expa
    @8
    @31
    wch
    wi
    vx
    @30
    @19
    cvv
    wcel
    @30
    cvv
    wcel
    vy
    vex
    @19
    @29
    cvv
    difexg
    ax-mp
    @0
    @30
    wceq
    @7
    @31
    wph
    wch
    @0
    @30
    @6
    cen
    breq1
    findcard.2
    imbi12d
    spcv
    syl5com
    ralrimdva
    imp
    an32s
    3impa
    findcard.6
    sylc
    3exp
    alrimdv
    @12
    @21
    vx
    vy
    @0
    @19
    wceq
    @11
    @20
    wph
    wth
    @0
    @19
    @10
    cen
    breq1
    findcard.3
    imbi12d
    cbvalv
    syl6ibr
    finds1
    19.21bi
    rexlimiv
    sylbi
    vtoclga
end
