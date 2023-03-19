include "clsi.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cmpt.mm"
include "crn.mm"
include "csup.mm"
include "cc0.mm"
include "csn.mm"
include "wceq.mm"
include "wtru.mm"
include "cn.mm"
include "cvv.mm"
include "nftru.mm"
include "wcel.mm"
include "nnex.mm"
include "a1i.mm"
include "wf.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "cif.mm"
include "0xr.mm"
include "1re.mm"
include "rexri.mm"
include "ifcld.mm"
include "fmpti.mm"
include "eqid.mm"
include "liminfval5.mm"
include "trud.mm"
include "cpr.mm"
include "id.mm"
include "limsup10exlem.mm"
include "infeq1d.mm"
include "wor.mm"
include "xrltso.mm"
include "infpr.mm"
include "mp3an.mm"
include "0lt1.mm"
include "iftruei.mm"
include "eqtri.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "rneqi.mm"
include "wa.mm"
include "0re.mm"
include "c0.mm"
include "wne.mm"
include "ren0.mm"
include "rnmptc.mm"
include "supeq1i.mm"
include "supsn.mm"
include "mp2an.mm"
include "3eqtri.mm"

theorem liminf10ex
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume liminf10ex.1: |- F = ( n e. NN |-> if ( 2 || n , 0 , 1 ) )


  assert |- ( liminf ` F ) = 0

  proof
    cF
    clsi
    cfv
    #
    vk
    cr
    cF
    vk
    cv
    #
    cpnf
    cico
    co
    cima
    #
    cxr
    clt
    cinf
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cc0
    csn
    #
    cxr
    clt
    csup
    #
    cc0
    @0
    @6
    wceq
    wtru
    cn
    vk
    cF
    @4
    cvv
    vk
    nftru
    cn
    cvv
    wcel
    wtru
    nnex
    a1i
    cn
    cxr
    cF
    wf
    wtru
    vn
    cn
    cxr
    c2
    vn
    cv
    #
    cdvds
    wbr
    #
    cc0
    c1
    cif
    cF
    liminf10ex.1
    @9
    cn
    wcel
    #
    @10
    cc0
    c1
    cxr
    cc0
    cxr
    wcel
    #
    @11
    0xr
    a1i
    c1
    cxr
    wcel
    #
    @11
    c1
    1re
    rexri
    #
    a1i
    ifcld
    fmpti
    a1i
    @4
    eqid
    liminfval5
    trud
    cxr
    @5
    @7
    clt
    @5
    vk
    cr
    cc0
    cmpt
    #
    crn
    #
    @7
    @4
    @15
    vk
    cr
    @3
    cc0
    @1
    cr
    wcel
    #
    @3
    cc0
    c1
    cpr
    #
    cxr
    clt
    cinf
    #
    cc0
    @17
    cxr
    @2
    @18
    clt
    @17
    vn
    cF
    @1
    liminf10ex.1
    @17
    id
    limsup10exlem
    infeq1d
    @19
    cc0
    wceq
    @17
    @19
    cc0
    c1
    clt
    wbr
    #
    cc0
    c1
    cif
    #
    cc0
    cxr
    clt
    wor
    #
    @12
    @13
    @19
    @21
    wceq
    xrltso
    0xr
    @14
    cxr
    cc0
    c1
    clt
    infpr
    mp3an
    @20
    cc0
    c1
    0lt1
    iftruei
    eqtri
    a1i
    eqtrd
    mpteq2ia
    rneqi
    @16
    @7
    wceq
    wtru
    vk
    cr
    cc0
    cr
    @15
    @15
    eqid
    cc0
    cr
    wcel
    wtru
    @17
    wa
    0re
    a1i
    cr
    c0
    wne
    wtru
    ren0
    a1i
    rnmptc
    trud
    eqtri
    supeq1i
    @22
    @12
    @8
    cc0
    wceq
    xrltso
    0xr
    cxr
    cc0
    clt
    supsn
    mp2an
    3eqtri
end
