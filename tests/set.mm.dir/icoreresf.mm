include "cr.mm"
include "cxp.mm"
include "cpw.mm"
include "cico.mm"
include "cres.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "cxr.mm"
include "rexpssxrxp.mm"
include "wb.mm"
include "cle.mm"
include "clt.mm"
include "df-ico.mm"
include "ixxf.mm"
include "ffn.mm"
include "fnssresb.mm"
include "mp2b.mm"
include "mpbir.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "crab.mm"
include "cmpt2.mm"
include "eqid.mm"
include "icorempt2.mm"
include "rneqi.mm"
include "wcel.mm"
include "wral.mm"
include "ssrab2.mm"
include "reex.mm"
include "elpw2.mm"
include "rgen2w.mm"
include "wceq.mm"
include "wrex.mm"
include "rnmpt2.mm"
include "abeq2i.mm"
include "simpl.mm"
include "simpr.mm"
include "r19.29d2r.mm"
include "wi.mm"
include "eleq1.mm"
include "biimparc.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "syl.mm"
include "ex.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "df-f.mm"
include "mpbir2an.mm"

theorem icoreresf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vl: setvar l


  assert |- ( [,) |` ( RR X. RR ) ) : ( RR X. RR ) --> ~P RR

  proof
    cr
    cr
    cxp
    #
    cr
    cpw
    #
    cico
    @0
    cres
    #
    wf
    @2
    @0
    wfn
    #
    @2
    crn
    #
    @1
    wss
    @3
    @0
    cxr
    cxr
    cxp
    #
    wss
    #
    rexpssxrxp
    @5
    cxr
    cpw
    #
    cico
    wf
    cico
    @5
    wfn
    @3
    @6
    wb
    vx
    vy
    vz
    cle
    clt
    cico
    vx
    vy
    vz
    df-ico
    ixxf
    @5
    @7
    cico
    ffn
    @5
    @0
    cico
    fnssresb
    mp2b
    mpbir
    @4
    vx
    vy
    cr
    cr
    vx
    cv
    #
    vz
    cv
    #
    cle
    wbr
    @9
    vy
    cv
    #
    clt
    wbr
    wa
    #
    vz
    cr
    crab
    #
    cmpt2
    #
    crn
    #
    @1
    @2
    @13
    vx
    vy
    vz
    @2
    @2
    eqid
    icorempt2
    rneqi
    @12
    @1
    wcel
    #
    vy
    cr
    wral
    vx
    cr
    wral
    #
    @14
    @1
    wss
    @15
    vx
    vy
    cr
    cr
    @15
    @12
    cr
    wss
    @11
    vz
    cr
    ssrab2
    @12
    cr
    reex
    elpw2
    mpbir
    rgen2w
    @16
    vl
    @14
    @1
    vl
    cv
    #
    @14
    wcel
    @17
    @12
    wceq
    #
    vy
    cr
    wrex
    vx
    cr
    wrex
    #
    @16
    @17
    @1
    wcel
    #
    @19
    vl
    @14
    vx
    vy
    vl
    cr
    cr
    @12
    @13
    @13
    eqid
    rnmpt2
    abeq2i
    @16
    @19
    @20
    @16
    @19
    wa
    #
    @15
    @18
    wa
    #
    vy
    cr
    wrex
    vx
    cr
    wrex
    @20
    @21
    @15
    @18
    vx
    vy
    cr
    cr
    @16
    @19
    simpl
    @16
    @19
    simpr
    r19.29d2r
    @22
    @20
    vx
    vy
    cr
    cr
    @22
    @20
    wi
    @8
    cr
    wcel
    @10
    cr
    wcel
    wa
    @18
    @20
    @15
    @17
    @12
    @1
    eleq1
    biimparc
    a1i
    rexlimivv
    syl
    ex
    syl5bi
    ssrdv
    ax-mp
    eqsstri
    @0
    @1
    @2
    df-f
    mpbir2an
end
