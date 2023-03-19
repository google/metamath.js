include "cch.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "cph.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "crio.mm"
include "cpjh.mm"
include "wreu.mm"
include "wmo.mm"
include "csh.mm"
include "wb.mm"
include "chsh.mm"
include "shocsh.mm"
include "syl.mm"
include "shsel.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "cin.mm"
include "c0h.mm"
include "ocin.mm"
include "pjhthmo.mm"
include "syl3anc.mm"
include "adantr.mm"
include "wrmo.mm"
include "reu5.mm"
include "df-rmo.mm"
include "anbi2i.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "riotacl.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "pm4.71rd.mm"
include "chil.mm"
include "wss.mm"
include "shsss.mm"
include "sselda.mm"
include "pjhval.mm"
include "syldan.mm"
include "eqeq1d.mm"
include "id.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "riota2.mm"
include "syl2anr.mm"
include "pm5.32da.mm"
include "3bitr4d.mm"

theorem pjpreeq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cH: class H
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z

  disjoint H x
  disjoint A x
  disjoint B x
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint H h
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint H y
  disjoint H z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( ( H e. CH /\ A e. ( H +H ( _|_ ` H ) ) ) -> ( ( ( projh ` H ) ` A ) = B <-> ( B e. H /\ E. x e. ( _|_ ` H ) A = ( B +h x ) ) ) )

  proof
    cH
    cch
    wcel
    #
    cA
    cH
    cH
    cort
    cfv
    #
    cph
    co
    #
    wcel
    #
    wa
    #
    cA
    vy
    cv
    #
    vx
    cv
    #
    cva
    co
    #
    wceq
    #
    vx
    @1
    wrex
    #
    vy
    cH
    crio
    #
    cB
    wceq
    #
    cB
    cH
    wcel
    #
    @11
    wa
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cB
    wceq
    @12
    cA
    cB
    @6
    cva
    co
    #
    wceq
    #
    vx
    @1
    wrex
    #
    wa
    @4
    @11
    @12
    @4
    @10
    cH
    wcel
    #
    @11
    @12
    @4
    @9
    vy
    cH
    wreu
    #
    @17
    @4
    @9
    vy
    cH
    wrex
    #
    @5
    cH
    wcel
    @9
    wa
    vy
    wmo
    #
    @18
    @0
    @3
    @19
    @0
    cH
    csh
    wcel
    #
    @1
    csh
    wcel
    #
    @3
    @19
    wb
    cH
    chsh
    #
    @0
    @21
    @22
    @23
    cH
    shocsh
    syl
    #
    vy
    vx
    cH
    @1
    cA
    shsel
    syl2anc
    biimpa
    @0
    @20
    @3
    @0
    @21
    @22
    cH
    @1
    cin
    c0h
    wceq
    #
    @20
    @23
    @24
    @0
    @21
    @25
    @23
    cH
    ocin
    syl
    vy
    vx
    cH
    @1
    cA
    pjhthmo
    syl3anc
    adantr
    @18
    @19
    @9
    vy
    cH
    wrmo
    #
    wa
    @19
    @20
    wa
    @9
    vy
    cH
    reu5
    @26
    @20
    @19
    @9
    vy
    cH
    df-rmo
    anbi2i
    bitri
    sylanbrc
    #
    @9
    vy
    cH
    riotacl
    syl
    @10
    cB
    cH
    eleq1
    syl5ibcom
    pm4.71rd
    @4
    @13
    @10
    cB
    @0
    @3
    cA
    chil
    wcel
    @13
    @10
    wceq
    @0
    @2
    chil
    cA
    @0
    @21
    @22
    @2
    chil
    wss
    @23
    @24
    cH
    @1
    shsss
    syl2anc
    sselda
    vy
    vx
    cA
    cH
    pjhval
    syldan
    eqeq1d
    @4
    @12
    @16
    @11
    @12
    @12
    @18
    @16
    @11
    wb
    @4
    @12
    id
    @27
    @9
    @16
    vy
    cH
    cB
    @5
    cB
    wceq
    #
    @8
    @15
    vx
    @1
    @28
    @7
    @14
    cA
    @5
    cB
    @6
    cva
    oveq1
    eqeq2d
    rexbidv
    riota2
    syl2anr
    pm5.32da
    3bitr4d
end
