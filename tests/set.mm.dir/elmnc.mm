include "cmnc.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "cply.mm"
include "cdgr.mm"
include "ccoe.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cdm.mm"
include "cpw.mm"
include "cv.mm"
include "crab.mm"
include "df-mnc.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "elpwid.mm"
include "plybss.mm"
include "adantr.mm"
include "cnex.mm"
include "elpw2.mm"
include "fveq2.mm"
include "rabeq.mm"
include "syl.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "sylbir.mm"
include "eleq2d.mm"
include "fveq12d.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem elmnc
  let cP: class P
  let cS: class S
  let vs: setvar s
  let vp: setvar p


  assert |- ( P e. ( Monic ` S ) <-> ( P e. ( Poly ` S ) /\ ( ( coeff ` P ) ` ( deg ` P ) ) = 1 ) )

  proof
    cP
    cS
    cmnc
    cfv
    #
    wcel
    #
    cS
    cc
    wss
    #
    cP
    cS
    cply
    cfv
    #
    wcel
    #
    cP
    cdgr
    cfv
    #
    cP
    ccoe
    cfv
    #
    cfv
    #
    c1
    wceq
    #
    wa
    #
    @1
    cS
    cc
    @1
    cmnc
    cdm
    cc
    cpw
    #
    cS
    vs
    @10
    vp
    cv
    #
    cdgr
    cfv
    #
    @11
    ccoe
    cfv
    #
    cfv
    #
    c1
    wceq
    #
    vp
    vs
    cv
    #
    cply
    cfv
    #
    crab
    #
    cmnc
    vs
    vp
    df-mnc
    #
    dmmptss
    cP
    cS
    cmnc
    elfvdm
    sseldi
    elpwid
    @4
    @2
    @8
    cS
    cP
    plybss
    adantr
    @2
    @1
    cP
    @15
    vp
    @3
    crab
    #
    wcel
    @9
    @2
    @0
    @20
    cP
    @2
    cS
    @10
    wcel
    @0
    @20
    wceq
    cS
    cc
    cnex
    elpw2
    vs
    cS
    @18
    @20
    @10
    cmnc
    @16
    cS
    wceq
    @17
    @3
    wceq
    @18
    @20
    wceq
    @16
    cS
    cply
    fveq2
    @15
    vp
    @17
    @3
    rabeq
    syl
    @19
    @15
    vp
    @3
    cS
    cply
    fvex
    rabex
    fvmpt
    sylbir
    eleq2d
    @15
    @8
    vp
    cP
    @3
    @11
    cP
    wceq
    #
    @14
    @7
    c1
    @21
    @12
    @5
    @13
    @6
    @11
    cP
    ccoe
    fveq2
    @11
    cP
    cdgr
    fveq2
    fveq12d
    eqeq1d
    elrab
    syl6bb
    pm5.21nii
end
