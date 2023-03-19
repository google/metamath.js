include "cz.mm"
include "wcel.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "clm.mm"
include "cli.mm"
include "3anass.mm"
include "wb.mm"
include "uztrn2.mm"
include "simplr.mm"
include "sselda.mm"
include "biantrurd.mm"
include "wceq.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "ancoms.mm"
include "breq1d.mm"
include "pm5.32da.mm"
include "ad2antlr.mm"
include "bitr3d.mm"
include "syl5bb.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "cnfldtopn.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "a1i.mm"
include "simpl.mm"
include "lmmbr3.mm"
include "simpll.mm"
include "simpr.mm"
include "eqidd.mm"
include "clim2.mm"
include "3bitr4d.mm"

theorem lmclim
  let cP: class P
  let cF: class F
  let cJ: class J
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume lmclim.2: |- J = ( TopOpen ` CCfld )
  assume lmclim.3: |- Z = ( ZZ>= ` M )


  assert |- ( ( M e. ZZ /\ Z C_ dom F ) -> ( F ( ~~>t ` J ) P <-> ( F e. ( CC ^pm CC ) /\ F ~~> P ) ) )

  proof
    cM
    cz
    wcel
    #
    cZ
    cF
    cdm
    #
    wss
    #
    wa
    #
    cF
    cc
    cc
    cpm
    co
    #
    wcel
    #
    cP
    cc
    wcel
    #
    vk
    cv
    #
    @1
    wcel
    #
    @7
    cF
    cfv
    #
    cc
    wcel
    #
    @9
    cP
    cabs
    cmin
    ccom
    #
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    w3a
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    w3a
    #
    @5
    @6
    @10
    @9
    cP
    cmin
    co
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    wa
    #
    vk
    @17
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    wa
    #
    cF
    cP
    cJ
    clm
    cfv
    wbr
    @5
    cF
    cP
    cli
    wbr
    #
    wa
    @21
    @5
    @6
    @20
    wa
    #
    wa
    @3
    @29
    @5
    @6
    @20
    3anass
    @3
    @31
    @28
    @5
    @3
    @6
    @20
    @27
    @3
    @6
    wa
    #
    @19
    @26
    vx
    crp
    @32
    @18
    @25
    vj
    cZ
    @32
    @16
    cZ
    wcel
    #
    wa
    @15
    @24
    vk
    @17
    @32
    @33
    @7
    @17
    wcel
    #
    @15
    @24
    wb
    #
    @33
    @34
    wa
    @32
    @7
    cZ
    wcel
    #
    @35
    cM
    @7
    @16
    cZ
    lmclim.3
    uztrn2
    @15
    @8
    @10
    @14
    wa
    #
    wa
    #
    @32
    @36
    wa
    #
    @24
    @8
    @10
    @14
    3anass
    @39
    @37
    @38
    @24
    @39
    @8
    @37
    @32
    cZ
    @1
    @7
    @0
    @2
    @6
    simplr
    sselda
    biantrurd
    @6
    @37
    @24
    wb
    @3
    @36
    @6
    @10
    @14
    @23
    @6
    @10
    wa
    @12
    @22
    @13
    clt
    @10
    @6
    @12
    @22
    wceq
    @9
    cP
    @11
    @11
    eqid
    cnmetdval
    ancoms
    breq1d
    pm5.32da
    ad2antlr
    bitr3d
    syl5bb
    sylan2
    anassrs
    ralbidva
    rexbidva
    ralbidv
    pm5.32da
    anbi2d
    syl5bb
    @3
    vx
    @11
    cP
    vj
    vk
    cF
    cJ
    cM
    cc
    cZ
    cJ
    lmclim.2
    cnfldtopn
    @11
    cc
    cxmt
    cfv
    wcel
    @3
    cnxmet
    a1i
    lmclim.3
    @0
    @2
    simpl
    lmmbr3
    @3
    @5
    @30
    @28
    @3
    @5
    wa
    #
    vx
    cP
    @9
    vj
    vk
    cF
    cM
    @4
    cZ
    lmclim.3
    @0
    @2
    @5
    simpll
    @3
    @5
    simpr
    @40
    @36
    wa
    @9
    eqidd
    clim2
    pm5.32da
    3bitr4d
end
