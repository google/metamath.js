include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "wex.mm"
include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wreu.mm"
include "wrex.mm"
include "wral.mm"
include "nfv.mm"
include "eu2.mm"
include "df-reu.mm"
include "df-rex.mm"
include "df-ral.mm"
include "19.21v.mm"
include "nfs1v.mm"
include "nfan.mm"
include "eleq1.mm"
include "sbequ12.mm"
include "anbi12d.mm"
include "sbie.mm"
include "anbi2i.mm"
include "an4.mm"
include "bitri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "3bitri.mm"
include "albii.mm"
include "imbi2i.mm"
include "3bitr4i.mm"
include "bitr4i.mm"
include "anbi12i.mm"

theorem reu2
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
  assert |- ( E! x e. A ph <-> ( E. x e. A ph /\ A. x e. A A. y e. A ( ( ph /\ [ y / x ] ph ) -> x = y ) ) )

  proof
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
    @2
    vx
    wex
    #
    @2
    @2
    vx
    vy
    wsb
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    wa
    wph
    vx
    cA
    wreu
    wph
    vx
    cA
    wrex
    #
    wph
    wph
    vx
    vy
    wsb
    #
    wa
    #
    @6
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wa
    @2
    vx
    vy
    @2
    vy
    nfv
    eu2
    wph
    vx
    cA
    df-reu
    @10
    @3
    @15
    @9
    wph
    vx
    cA
    df-rex
    @15
    @1
    @14
    wi
    #
    vx
    wal
    @9
    @14
    vx
    cA
    df-ral
    @8
    @16
    vx
    @1
    vy
    cv
    #
    cA
    wcel
    #
    @13
    wi
    #
    wi
    #
    vy
    wal
    @1
    @19
    vy
    wal
    #
    wi
    @8
    @16
    @1
    @19
    vy
    19.21v
    @7
    @20
    vy
    @7
    @1
    @18
    wa
    #
    @12
    wa
    #
    @6
    wi
    @22
    @13
    wi
    @20
    @5
    @23
    @6
    @5
    @2
    @18
    @11
    wa
    #
    wa
    @23
    @4
    @24
    @2
    @2
    @24
    vx
    vy
    @18
    @11
    vx
    @18
    vx
    nfv
    wph
    vx
    vy
    nfs1v
    nfan
    @6
    @1
    @18
    wph
    @11
    @0
    @17
    cA
    eleq1
    wph
    vx
    vy
    sbequ12
    anbi12d
    sbie
    anbi2i
    @1
    wph
    @18
    @11
    an4
    bitri
    imbi1i
    @22
    @12
    @6
    impexp
    @1
    @18
    @13
    impexp
    3bitri
    albii
    @14
    @21
    @1
    @13
    vy
    cA
    df-ral
    imbi2i
    3bitr4i
    albii
    bitr4i
    anbi12i
    3bitr4i
end
