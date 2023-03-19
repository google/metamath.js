include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "crn.mm"
include "cinf.mm"
include "c1.mm"
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
include "cc0.mm"
include "cif.mm"
include "0xr.mm"
include "1re.mm"
include "rexri.mm"
include "ifcld.mm"
include "fmpti.mm"
include "eqid.mm"
include "limsupval3.mm"
include "trud.mm"
include "cpr.mm"
include "id.mm"
include "limsup10exlem.mm"
include "supeq1d.mm"
include "wor.mm"
include "xrltso.mm"
include "suppr.mm"
include "mp3an.mm"
include "cle.mm"
include "wn.mm"
include "0le1.mm"
include "wb.mm"
include "0re.mm"
include "lenlt.mm"
include "mp2an.mm"
include "mpbi.mm"
include "iffalsei.mm"
include "eqtri.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "rneqi.mm"
include "wa.mm"
include "elexi.mm"
include "c0.mm"
include "wne.mm"
include "ren0.mm"
include "rnmptc.mm"
include "infeq1i.mm"
include "infsn.mm"
include "3eqtri.mm"

theorem limsup10ex
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume limsup10ex.1: |- F = ( n e. NN |-> if ( 2 || n , 0 , 1 ) )


  assert |- ( limsup ` F ) = 1

  proof
    cF
    clsp
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
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    c1
    csn
    #
    cxr
    clt
    cinf
    #
    c1
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
    limsup10ex.1
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
    limsupval3
    trud
    cxr
    @5
    @7
    clt
    @5
    vk
    cr
    c1
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
    c1
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
    csup
    #
    c1
    @17
    cxr
    @2
    @18
    clt
    @17
    vn
    cF
    @1
    limsup10ex.1
    @17
    id
    limsup10exlem
    supeq1d
    @19
    c1
    wceq
    @17
    @19
    c1
    cc0
    clt
    wbr
    #
    cc0
    c1
    cif
    #
    c1
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
    suppr
    mp3an
    @20
    cc0
    c1
    cc0
    c1
    cle
    wbr
    #
    @20
    wn
    #
    0le1
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @23
    @24
    wb
    0re
    1re
    cc0
    c1
    lenlt
    mp2an
    mpbi
    iffalsei
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
    c1
    cvv
    @15
    @15
    eqid
    c1
    cvv
    wcel
    wtru
    @17
    wa
    c1
    cr
    1re
    elexi
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
    infeq1i
    @22
    @13
    @8
    c1
    wceq
    xrltso
    @14
    cxr
    c1
    clt
    infsn
    mp2an
    3eqtri
end
