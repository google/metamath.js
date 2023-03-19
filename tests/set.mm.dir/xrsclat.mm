include "cxrs.mm"
include "ccla.mm"
include "wcel.mm"
include "cpo.mm"
include "club.mm"
include "cfv.mm"
include "cdm.mm"
include "cxr.mm"
include "cpw.mm"
include "wceq.mm"
include "cglb.mm"
include "wa.mm"
include "ctos.mm"
include "xrstos.mm"
include "tospos.mm"
include "ax-mp.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wreu.mm"
include "crab.mm"
include "xrsbas.mm"
include "xrsle.mm"
include "eqid.mm"
include "biid.mm"
include "lubdm.mm"
include "rabid2.mm"
include "wss.mm"
include "selpw.mm"
include "clt.mm"
include "wn.mm"
include "wrex.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "xrsupss.mm"
include "supeu.mm"
include "xrslt.mm"
include "id.mm"
include "toslublem.mm"
include "reubidva.mm"
include "mpbird.mm"
include "sylbi.mm"
include "mprgbir.mm"
include "eqtr4i.mm"
include "glbdm.mm"
include "ccnv.mm"
include "cnvso.mm"
include "mpbi.mm"
include "xrinfmss2.mm"
include "tosglblem.mm"
include "pm3.2i.mm"
include "isclat.mm"
include "mpbir2an.mm"

theorem xrsclat
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x


  assert |- RR*s e. CLat

  proof
    cxrs
    ccla
    wcel
    cxrs
    cpo
    wcel
    #
    cxrs
    club
    cfv
    #
    cdm
    #
    cxr
    cpw
    #
    wceq
    #
    cxrs
    cglb
    cfv
    #
    cdm
    #
    @3
    wceq
    #
    wa
    cxrs
    ctos
    wcel
    #
    @0
    xrstos
    cxrs
    tospos
    #
    ax-mp
    @4
    @7
    @2
    vb
    cv
    #
    va
    cv
    #
    cle
    wbr
    vb
    vx
    cv
    #
    wral
    @10
    vc
    cv
    #
    cle
    wbr
    vb
    @12
    wral
    @11
    @13
    cle
    wbr
    wi
    vc
    cxr
    wral
    wa
    #
    va
    cxr
    wreu
    #
    vx
    @3
    crab
    #
    @3
    @8
    @2
    @16
    wceq
    xrstos
    @8
    @14
    va
    vb
    vc
    cxr
    @1
    cxrs
    cle
    cpo
    vx
    xrsbas
    xrsle
    @1
    eqid
    #
    @14
    biid
    @9
    lubdm
    ax-mp
    @3
    @16
    wceq
    @15
    vx
    @3
    @15
    vx
    @3
    rabid2
    @12
    @3
    wcel
    #
    @12
    cxr
    wss
    #
    @15
    vx
    cxr
    selpw
    #
    @19
    @15
    @11
    @10
    clt
    wbr
    wn
    vb
    @12
    wral
    @10
    @11
    clt
    wbr
    @10
    vd
    cv
    #
    clt
    wbr
    vd
    @12
    wrex
    wi
    vb
    cxr
    wral
    wa
    #
    va
    cxr
    wreu
    @19
    va
    vb
    vd
    cxr
    @12
    clt
    cxr
    clt
    wor
    #
    @19
    xrltso
    a1i
    va
    vb
    vd
    @12
    xrsupss
    supeu
    @19
    @14
    @22
    va
    cxr
    @19
    @12
    cxr
    clt
    cxrs
    cle
    va
    vb
    vc
    vd
    xrsbas
    xrslt
    @8
    @19
    xrstos
    a1i
    #
    @19
    id
    #
    xrsle
    toslublem
    reubidva
    mpbird
    sylbi
    mprgbir
    eqtr4i
    @6
    @11
    @10
    cle
    wbr
    vb
    @12
    wral
    @13
    @10
    cle
    wbr
    vb
    @12
    wral
    @13
    @11
    cle
    wbr
    wi
    vc
    cxr
    wral
    wa
    #
    va
    cxr
    wreu
    #
    vx
    @3
    crab
    #
    @3
    @8
    @6
    @28
    wceq
    xrstos
    @8
    @26
    va
    vb
    vc
    cxr
    @5
    cxrs
    cle
    cpo
    vx
    xrsbas
    xrsle
    @5
    eqid
    #
    @26
    biid
    @9
    glbdm
    ax-mp
    @3
    @28
    wceq
    @27
    vx
    @3
    @27
    vx
    @3
    rabid2
    @18
    @19
    @27
    @20
    @19
    @27
    @11
    @10
    clt
    ccnv
    #
    wbr
    wn
    vb
    @12
    wral
    @10
    @11
    @30
    wbr
    @10
    @21
    @30
    wbr
    vd
    @12
    wrex
    wi
    vb
    cxr
    wral
    wa
    #
    va
    cxr
    wreu
    @19
    va
    vb
    vd
    cxr
    @12
    @30
    cxr
    @30
    wor
    #
    @19
    @23
    @32
    xrltso
    cxr
    clt
    cnvso
    mpbi
    a1i
    va
    vb
    vd
    @12
    xrinfmss2
    supeu
    @19
    @26
    @31
    va
    cxr
    @19
    @12
    cxr
    clt
    cxrs
    cle
    va
    vb
    vc
    vd
    xrsbas
    xrslt
    @24
    @25
    xrsle
    tosglblem
    reubidva
    mpbird
    sylbi
    mprgbir
    eqtr4i
    pm3.2i
    cxr
    @1
    @5
    cxrs
    xrsbas
    @17
    @29
    isclat
    mpbir2an
end
