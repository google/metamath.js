include "ctpos.mm"
include "cdm.mm"
include "wrel.mm"
include "c0.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "0ex.mm"
include "eldm.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "brtpos0.mm"
include "ax-mp.mm"
include "cxp.mm"
include "0nelxp.mm"
include "wss.mm"
include "wi.mm"
include "df-rel.mm"
include "ssel.mm"
include "sylbi.mm"
include "mtoi.mm"
include "breldm.mm"
include "nsyl3.mm"
include "sylbir.mm"
include "exlimiv.mm"
include "con2i.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "relcnv.mm"
include "mpbi.mm"
include "sseli.mm"
include "a1i.mm"
include "elsni.mm"
include "breq1d.mm"
include "pm2.24d.mm"
include "syl6bi.mm"
include "com3l.mm"
include "impcom.mm"
include "wo.mm"
include "cun.mm"
include "cuni.mm"
include "brtpos2.mm"
include "simplbi.mm"
include "elun.mm"
include "sylib.mm"
include "adantl.mm"
include "mpjaod.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "sylibr.mm"
include "impbii.mm"

theorem reldmtpos
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( Rel dom tpos F <-> -. (/) e. dom F )

  proof
    cF
    ctpos
    #
    cdm
    #
    wrel
    #
    c0
    cF
    cdm
    #
    wcel
    #
    wn
    #
    @4
    @2
    @4
    c0
    vy
    cv
    #
    cF
    wbr
    #
    vy
    wex
    @2
    wn
    #
    vy
    c0
    cF
    0ex
    eldm
    @7
    @8
    vy
    @7
    c0
    @6
    @0
    wbr
    #
    @8
    @6
    cvv
    wcel
    #
    @9
    @7
    wb
    vy
    vex
    #
    @6
    cF
    cvv
    brtpos0
    ax-mp
    #
    @2
    c0
    @1
    wcel
    #
    @9
    @2
    @13
    c0
    cvv
    cvv
    cxp
    #
    wcel
    #
    cvv
    cvv
    0nelxp
    @2
    @1
    @14
    wss
    #
    @13
    @15
    wi
    @1
    df-rel
    #
    @1
    @14
    c0
    ssel
    sylbi
    mtoi
    c0
    @6
    @0
    0ex
    @11
    breldm
    nsyl3
    sylbir
    exlimiv
    sylbi
    con2i
    @5
    @16
    @2
    @5
    vx
    @1
    @14
    vx
    cv
    #
    @1
    wcel
    @18
    @6
    @0
    wbr
    #
    vy
    wex
    @5
    @18
    @14
    wcel
    #
    vy
    @18
    @0
    vx
    vex
    eldm
    @5
    @19
    @20
    vy
    @5
    @19
    @20
    @5
    @19
    wa
    #
    @18
    @3
    ccnv
    #
    wcel
    #
    @20
    @18
    c0
    csn
    #
    wcel
    #
    @23
    @20
    wi
    @21
    @22
    @14
    @18
    @22
    wrel
    @22
    @14
    wss
    @3
    relcnv
    @22
    df-rel
    mpbi
    sseli
    a1i
    @19
    @5
    @25
    @20
    wi
    @25
    @19
    @5
    @20
    @25
    @19
    @9
    @5
    @20
    wi
    #
    @25
    @18
    c0
    @6
    @0
    @18
    c0
    elsni
    breq1d
    @9
    @7
    @26
    @12
    @7
    @4
    @20
    c0
    @6
    cF
    0ex
    @11
    breldm
    pm2.24d
    sylbi
    syl6bi
    com3l
    impcom
    @19
    @23
    @25
    wo
    #
    @5
    @19
    @18
    @22
    @24
    cun
    wcel
    #
    @27
    @19
    @28
    @18
    csn
    ccnv
    cuni
    @6
    cF
    wbr
    #
    @10
    @19
    @28
    @29
    wa
    wb
    @11
    @18
    @6
    cF
    cvv
    brtpos2
    ax-mp
    simplbi
    @18
    @22
    @24
    elun
    sylib
    adantl
    mpjaod
    ex
    exlimdv
    syl5bi
    ssrdv
    @17
    sylibr
    impbii
end
