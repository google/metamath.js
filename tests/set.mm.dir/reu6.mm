include "wreu.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "weq.mm"
include "wb.mm"
include "wral.mm"
include "wrex.mm"
include "df-reu.mm"
include "wal.mm"
include "wex.mm"
include "wi.mm"
include "19.28v.mm"
include "wsb.mm"
include "eleq1.mm"
include "sbequ12.mm"
include "anbi12d.mm"
include "equequ1.mm"
include "bibi12d.mm"
include "equid.mm"
include "tbt.mm"
include "simpl.mm"
include "sylbir.mm"
include "syl6bi.mm"
include "spimv.mm"
include "ibar.mm"
include "bibi1d.mm"
include "biimprcd.mm"
include "sps.mm"
include "jca.mm"
include "axc4i.mm"
include "biimp.mm"
include "imim2i.mm"
include "impd.mm"
include "adantl.mm"
include "eleq1a.mm"
include "adantr.mm"
include "imp.mm"
include "biimpr.mm"
include "com23.mm"
include "adantll.mm"
include "jcai.mm"
include "ex.mm"
include "impbid.mm"
include "alimi.mm"
include "impbii.mm"
include "df-ral.mm"
include "anbi2i.mm"
include "3bitr4i.mm"
include "exbii.mm"
include "df-eu.mm"
include "df-rex.mm"
include "bitri.mm"

theorem reu6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let wps: wff ps

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint B x
  disjoint B y
  disjoint ps x
  assert |- ( E! x e. A ph <-> E. y e. A A. x e. A ( ph <-> x = y ) )

  proof
    wph
    vx
    cA
    wreu
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    weu
    #
    wph
    vx
    vy
    weq
    #
    wb
    #
    vx
    cA
    wral
    #
    vy
    cA
    wrex
    #
    wph
    vx
    cA
    df-reu
    @2
    @4
    wb
    #
    vx
    wal
    #
    vy
    wex
    vy
    cv
    #
    cA
    wcel
    #
    @6
    wa
    #
    vy
    wex
    @3
    @7
    @9
    @12
    vy
    @11
    @1
    @5
    wi
    #
    wa
    #
    vx
    wal
    #
    @11
    @13
    vx
    wal
    #
    wa
    @9
    @12
    @11
    @13
    vx
    19.28v
    @9
    @15
    @8
    @14
    vx
    @9
    @11
    @13
    @8
    @11
    vx
    vy
    @4
    @8
    @11
    wph
    vx
    vy
    wsb
    #
    wa
    #
    vy
    vy
    weq
    #
    wb
    #
    @11
    @4
    @2
    @18
    @4
    @19
    @4
    @1
    @11
    wph
    @17
    @0
    @10
    cA
    eleq1
    wph
    vx
    vy
    sbequ12
    anbi12d
    vx
    vy
    vy
    equequ1
    bibi12d
    @20
    @18
    @11
    @19
    @18
    vy
    equid
    tbt
    @11
    @17
    simpl
    sylbir
    syl6bi
    spimv
    @8
    @13
    vx
    @1
    @5
    @8
    @1
    wph
    @2
    @4
    @1
    wph
    ibar
    bibi1d
    biimprcd
    sps
    jca
    axc4i
    @14
    @8
    vx
    @14
    @2
    @4
    @13
    @2
    @4
    wi
    @11
    @13
    @1
    wph
    @4
    @5
    wph
    @4
    wi
    @1
    wph
    @4
    biimp
    imim2i
    impd
    adantl
    @14
    @4
    @2
    @14
    @4
    wa
    @1
    wph
    @14
    @4
    @1
    @11
    @4
    @1
    wi
    @13
    @10
    cA
    @0
    eleq1a
    adantr
    imp
    @13
    @4
    @1
    wph
    wi
    #
    @11
    @13
    @4
    @21
    @13
    @1
    @4
    wph
    @5
    @4
    wph
    wi
    @1
    wph
    @4
    biimpr
    imim2i
    com23
    imp
    adantll
    jcai
    ex
    impbid
    alimi
    impbii
    @6
    @16
    @11
    @5
    vx
    cA
    df-ral
    anbi2i
    3bitr4i
    exbii
    @2
    vx
    vy
    df-eu
    @6
    vy
    cA
    df-rex
    3bitr4i
    bitri
end
