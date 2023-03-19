include "cop.mm"
include "copab.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "wsbc.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "cv.mm"
include "wex.mm"
include "wn.mm"
include "vex.mm"
include "opnzi.mm"
include "simpl.mm"
include "eqcomd.mm"
include "necon3ai.mm"
include "ax-mp.mm"
include "nex.mm"
include "elopab.mm"
include "mtbir.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "opnz.mm"
include "sylib.mm"
include "sbcex.mm"
include "spesbc.mm"
include "exlimiv.mm"
include "syl.mm"
include "jca.mm"
include "wsb.mm"
include "wb.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "dfsbcq2.mm"
include "bibi12d.mm"
include "opeq2.mm"
include "sbcbidv.mm"
include "nfopab1.mm"
include "nfel2.mm"
include "nfs1v.mm"
include "nfbi.mm"
include "weq.mm"
include "sbequ12.mm"
include "nfopab2.mm"
include "opabid.mm"
include "chvar.mm"
include "vtocl2g.mm"
include "pm5.21nii.mm"

theorem opelopabsb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint B x
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint B w
  disjoint ph w
  disjoint ph z
  assert |- ( <. A , B >. e. { <. x , y >. | ph } <-> [. A / x ]. [. B / y ]. ph )

  proof
    cA
    cB
    cop
    #
    wph
    vx
    vy
    copab
    #
    wcel
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    wph
    vy
    cB
    wsbc
    #
    vx
    cA
    wsbc
    #
    @2
    @0
    c0
    wne
    @5
    @2
    @0
    c0
    @0
    c0
    wceq
    @2
    c0
    @1
    wcel
    #
    @8
    c0
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    @14
    vx
    @13
    vy
    @11
    c0
    wne
    @13
    wn
    @9
    @10
    vx
    vex
    vy
    vex
    opnzi
    @13
    @11
    c0
    @13
    c0
    @11
    @12
    wph
    simpl
    eqcomd
    necon3ai
    ax-mp
    nex
    nex
    wph
    vx
    vy
    c0
    elopab
    mtbir
    @0
    c0
    @1
    eleq1
    mtbiri
    necon2ai
    cA
    cB
    opnz
    sylib
    @7
    @3
    @4
    @6
    vx
    cA
    sbcex
    @7
    @6
    vx
    wex
    @4
    @6
    vx
    cA
    spesbc
    @6
    @4
    vx
    wph
    vy
    cB
    sbcex
    exlimiv
    syl
    jca
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    @1
    wcel
    #
    wph
    vy
    vw
    wsb
    #
    vx
    vz
    wsb
    #
    wb
    #
    cA
    @16
    cop
    #
    @1
    wcel
    #
    @19
    vx
    cA
    wsbc
    #
    wb
    @2
    @7
    wb
    vz
    vw
    cA
    cB
    cvv
    cvv
    @15
    cA
    wceq
    #
    @18
    @23
    @20
    @24
    @25
    @17
    @22
    @1
    @15
    cA
    @16
    opeq1
    eleq1d
    @19
    vx
    vz
    cA
    dfsbcq2
    bibi12d
    @16
    cB
    wceq
    #
    @23
    @2
    @24
    @7
    @26
    @22
    @0
    @1
    @16
    cB
    cA
    opeq2
    eleq1d
    @26
    @19
    @6
    vx
    cA
    wph
    vy
    vw
    cB
    dfsbcq2
    sbcbidv
    bibi12d
    @9
    @16
    cop
    #
    @1
    wcel
    #
    @19
    wb
    #
    @21
    vx
    vz
    @18
    @20
    vx
    vx
    @17
    @1
    wph
    vx
    vy
    nfopab1
    nfel2
    @19
    vx
    vz
    nfs1v
    nfbi
    vx
    vz
    weq
    #
    @28
    @18
    @19
    @20
    @30
    @27
    @17
    @1
    @9
    @15
    @16
    opeq1
    eleq1d
    @19
    vx
    vz
    sbequ12
    bibi12d
    @11
    @1
    wcel
    #
    wph
    wb
    @29
    vy
    vw
    @28
    @19
    vy
    vy
    @27
    @1
    wph
    vx
    vy
    nfopab2
    nfel2
    wph
    vy
    vw
    nfs1v
    nfbi
    vy
    vw
    weq
    #
    @31
    @28
    wph
    @19
    @32
    @11
    @27
    @1
    @10
    @16
    @9
    opeq2
    eleq1d
    wph
    vy
    vw
    sbequ12
    bibi12d
    wph
    vx
    vy
    opabid
    chvar
    chvar
    vtocl2g
    pm5.21nii
end
