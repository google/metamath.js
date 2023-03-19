include "cv.mm"
include "chli.mm"
include "wbr.mm"
include "chil.mm"
include "wrex.mm"
include "cims.mm"
include "cfv.mm"
include "cca.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "ccau.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cop.mm"
include "cmopn.mm"
include "clm.mm"
include "cdm.mm"
include "chlo.mm"
include "simpl.mm"
include "eqid.mm"
include "hlcompl.mm"
include "sylancr.mm"
include "wb.mm"
include "eldm2g.mm"
include "adantr.mm"
include "mpbid.mm"
include "df-br.mm"
include "wi.mm"
include "ctopon.mm"
include "cnv.mm"
include "cxmt.mm"
include "hlnvi.mm"
include "cva.mm"
include "csm.mm"
include "cno.mm"
include "cba.mm"
include "df-hba.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "imsxmet.mm"
include "mopntopon.mm"
include "mp2b.mm"
include "lmcl.mm"
include "mpan.mm"
include "a1i.mm"
include "cres.mm"
include "h2hlm.mm"
include "breqi.mm"
include "vex.mm"
include "brres.mm"
include "ancom.mm"
include "3bitri.mm"
include "baib.mm"
include "adantl.mm"
include "biimprd.mm"
include "jcad.mm"
include "syl5bir.mm"
include "eximdv.mm"
include "mpd.mm"
include "elin.mm"
include "df-rex.mm"
include "3imtr4i.mm"
include "h2hcau.mm"
include "eleq2s.mm"

theorem axhcompl-zf
  let vx: setvar x
  let cU: class U
  let cF: class F
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD

  disjoint F x
  disjoint U x
  assert |- ( F e. Cauchy -> E. x e. ~H F ~~>v x )

  proof
    cF
    vx
    cv
    #
    chli
    wbr
    #
    vx
    chil
    wrex
    #
    cF
    cU
    cims
    cfv
    #
    cca
    cfv
    #
    chil
    cn
    cmap
    co
    #
    cin
    #
    ccau
    cF
    @4
    wcel
    #
    cF
    @5
    wcel
    #
    wa
    #
    @0
    chil
    wcel
    #
    @1
    wa
    #
    vx
    wex
    #
    cF
    @6
    wcel
    @2
    @9
    cF
    @0
    cop
    @3
    cmopn
    cfv
    #
    clm
    cfv
    #
    wcel
    #
    vx
    wex
    #
    @12
    @9
    cF
    @14
    cdm
    wcel
    #
    @16
    @9
    cU
    chlo
    wcel
    @7
    @17
    axhil.2
    @7
    @8
    simpl
    @3
    cU
    cF
    @13
    @3
    eqid
    #
    @13
    eqid
    #
    hlcompl
    sylancr
    @7
    @17
    @16
    wb
    @8
    vx
    cF
    @14
    @4
    eldm2g
    adantr
    mpbid
    @9
    @15
    @11
    vx
    @15
    cF
    @0
    @14
    wbr
    #
    @9
    @11
    cF
    @0
    @14
    df-br
    @9
    @20
    @10
    @1
    @20
    @10
    wi
    @9
    @13
    chil
    ctopon
    cfv
    wcel
    #
    @20
    @10
    cU
    cnv
    wcel
    @3
    chil
    cxmt
    cfv
    wcel
    @21
    cU
    axhil.2
    hlnvi
    #
    @3
    cU
    chil
    chil
    cva
    csm
    cop
    cno
    cop
    #
    cba
    cfv
    cU
    cba
    cfv
    df-hba
    cU
    @23
    cba
    axhil.1
    fveq2i
    eqtr4i
    #
    @18
    imsxmet
    @3
    @13
    chil
    @19
    mopntopon
    mp2b
    @0
    cF
    @13
    chil
    lmcl
    mpan
    a1i
    @9
    @1
    @20
    @8
    @1
    @20
    wb
    @7
    @1
    @8
    @20
    @1
    cF
    @0
    @14
    @5
    cres
    #
    wbr
    @20
    @8
    wa
    @8
    @20
    wa
    cF
    @0
    chli
    @25
    @3
    cU
    @13
    axhil.1
    @22
    @24
    @18
    @19
    h2hlm
    breqi
    cF
    @0
    @14
    @5
    vx
    vex
    brres
    @20
    @8
    ancom
    3bitri
    baib
    adantl
    biimprd
    jcad
    syl5bir
    eximdv
    mpd
    cF
    @4
    @5
    elin
    @1
    vx
    chil
    df-rex
    3imtr4i
    @3
    cU
    axhil.1
    @22
    @24
    @18
    h2hcau
    eleq2s
end
