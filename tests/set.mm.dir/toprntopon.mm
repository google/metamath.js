include "ctop.mm"
include "ctopon.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cfv.mm"
include "toptopon2.mm"
include "biimpi.mm"
include "fvex.mm"
include "wceq.mm"
include "eleq2.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "wb.mm"
include "simpl.mm"
include "cvv.mm"
include "wfn.mm"
include "fntopon.mm"
include "vuniex.mm"
include "pm3.2i.mm"
include "fnfvelrn.mm"
include "ax-mp.mm"
include "jctr.mm"
include "impbii.mm"
include "a1i.mm"
include "bitrd.mm"
include "spcev.mm"
include "syl.mm"
include "cdm.mm"
include "wrex.mm"
include "wfun.mm"
include "wi.mm"
include "funtopon.mm"
include "elrnrexdm.mm"
include "rexex.mm"
include "anim2i.mm"
include "19.42v.mm"
include "biimpri.mm"
include "eqimss.mm"
include "sseld.mm"
include "com12.mm"
include "imp.mm"
include "eximi.mm"
include "topontop.mm"
include "ax5e.mm"
include "exlimiv.mm"
include "eluni.mm"
include "bicomi.mm"
include "bitri.mm"
include "eqriv.mm"

theorem toprntopon
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Top = U. ran TopOn

  proof
    vx
    ctop
    ctopon
    crn
    #
    cuni
    #
    vx
    cv
    #
    ctop
    wcel
    #
    @2
    vy
    cv
    #
    wcel
    #
    @4
    @0
    wcel
    #
    wa
    #
    vy
    wex
    #
    @2
    @1
    wcel
    #
    @3
    @8
    @3
    @2
    @2
    cuni
    #
    ctopon
    cfv
    #
    wcel
    #
    @8
    @3
    @12
    @2
    toptopon2
    biimpi
    @7
    @12
    vy
    @11
    @10
    ctopon
    fvex
    @4
    @11
    wceq
    #
    @7
    @12
    @11
    @0
    wcel
    #
    wa
    #
    @12
    @13
    @5
    @12
    @6
    @14
    @4
    @11
    @2
    eleq2
    @4
    @11
    @0
    eleq1
    anbi12d
    @15
    @12
    wb
    @13
    @15
    @12
    @12
    @14
    simpl
    @12
    @14
    ctopon
    cvv
    wfn
    #
    @10
    cvv
    wcel
    #
    wa
    @14
    @16
    @17
    fntopon
    vx
    vuniex
    pm3.2i
    cvv
    @10
    ctopon
    fnfvelrn
    ax-mp
    jctr
    impbii
    a1i
    bitrd
    spcev
    syl
    @7
    @3
    vy
    @7
    @2
    vz
    cv
    #
    ctopon
    cfv
    #
    wcel
    #
    vz
    wex
    #
    @3
    @7
    @5
    @4
    @19
    wceq
    #
    vz
    wex
    #
    wa
    #
    @21
    @6
    @23
    @5
    @6
    @22
    vz
    ctopon
    cdm
    #
    wrex
    #
    @23
    ctopon
    wfun
    @6
    @26
    wi
    funtopon
    vz
    ctopon
    @4
    elrnrexdm
    ax-mp
    @22
    vz
    @25
    rexex
    syl
    anim2i
    @24
    @5
    @22
    wa
    #
    vz
    wex
    #
    @21
    @28
    @24
    @5
    @22
    vz
    19.42v
    biimpri
    @27
    @20
    vz
    @5
    @22
    @20
    @22
    @5
    @20
    @22
    @4
    @19
    @2
    @4
    @19
    eqimss
    sseld
    com12
    imp
    eximi
    syl
    syl
    @21
    @3
    vz
    wex
    @3
    @20
    @3
    vz
    @18
    @2
    topontop
    eximi
    @3
    vz
    ax5e
    syl
    syl
    exlimiv
    impbii
    @9
    @8
    vy
    @2
    @0
    eluni
    bicomi
    bitri
    eqriv
end
