include "cdm.mm"
include "wcel.mm"
include "cpred.mm"
include "cv.mm"
include "wfn.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "ciun.mm"
include "wrex.mm"
include "cuni.mm"
include "cwrecs.mm"
include "df-wrecs.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "dmuni.mm"
include "eleq2i.mm"
include "eliun.mm"
include "bitri.mm"
include "wi.mm"
include "eqid.mm"
include "wfrlem1.mm"
include "abeq2i.mm"
include "predeq3.mm"
include "sseq1d.mm"
include "rspccv.mm"
include "adantl.mm"
include "wb.mm"
include "fndm.mm"
include "eleq2d.mm"
include "sseq2d.mm"
include "imbi12d.mm"
include "adantr.mm"
include "mpbird.mm"
include "adantrl.mm"
include "3adant3.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "reximia.mm"
include "ssiun.mm"
include "syl.mm"
include "syl6sseqr.mm"

theorem wfrdmcl
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wfrlem6.1: |- F = wrecs ( R , A , G )


  assert |- ( X e. dom F -> Pred ( R , A , X ) C_ dom F )

  proof
    cX
    cF
    cdm
    #
    wcel
    #
    cA
    cR
    cX
    cpred
    #
    vg
    vf
    cv
    #
    vx
    cv
    #
    wfn
    @4
    cA
    wss
    cA
    cR
    vy
    cv
    #
    cpred
    #
    @4
    wss
    vy
    @4
    wral
    wa
    @5
    @3
    cfv
    @3
    @6
    cres
    cG
    cfv
    wceq
    vy
    @4
    wral
    w3a
    vx
    wex
    vf
    cab
    #
    vg
    cv
    #
    cdm
    #
    ciun
    #
    @0
    @1
    cX
    @9
    wcel
    #
    vg
    @7
    wrex
    #
    @2
    @10
    wss
    #
    @1
    cX
    @10
    wcel
    @12
    @0
    @10
    cX
    @0
    @7
    cuni
    #
    cdm
    @10
    cF
    @14
    cF
    cA
    cR
    cG
    cwrecs
    @14
    wfrlem6.1
    vx
    vy
    cA
    cR
    vf
    cG
    df-wrecs
    eqtri
    dmeqi
    vg
    @7
    dmuni
    eqtri
    #
    eleq2i
    vg
    cX
    @7
    @9
    eliun
    bitri
    @12
    @2
    @9
    wss
    #
    vg
    @7
    wrex
    @13
    @11
    @16
    vg
    @7
    @8
    @7
    wcel
    @8
    vz
    cv
    #
    wfn
    #
    @17
    cA
    wss
    #
    cA
    cR
    vw
    cv
    #
    cpred
    #
    @17
    wss
    #
    vw
    @17
    wral
    #
    wa
    #
    @20
    @8
    cfv
    @8
    @21
    cres
    cG
    cfv
    wceq
    vw
    @17
    wral
    #
    w3a
    #
    vz
    wex
    #
    @11
    @16
    wi
    #
    @27
    vg
    @7
    vx
    vy
    vz
    vw
    cA
    @7
    cR
    vf
    vg
    cG
    @7
    eqid
    wfrlem1
    abeq2i
    @26
    @28
    vz
    @18
    @24
    @28
    @25
    @18
    @23
    @28
    @19
    @18
    @23
    wa
    @28
    cX
    @17
    wcel
    #
    @2
    @17
    wss
    #
    wi
    #
    @23
    @31
    @18
    @22
    @30
    vw
    cX
    @17
    @20
    cX
    wceq
    @21
    @2
    @17
    cA
    cR
    @20
    cX
    predeq3
    sseq1d
    rspccv
    adantl
    @18
    @28
    @31
    wb
    @23
    @18
    @11
    @29
    @16
    @30
    @18
    @9
    @17
    cX
    @17
    @8
    fndm
    #
    eleq2d
    @18
    @9
    @17
    @2
    @32
    sseq2d
    imbi12d
    adantr
    mpbird
    adantrl
    3adant3
    exlimiv
    sylbi
    reximia
    vg
    @7
    @9
    @2
    ssiun
    syl
    sylbi
    @15
    syl6sseqr
end
