include "crefld.mm"
include "cqqh.mm"
include "cfv.mm"
include "cq.mm"
include "cv.mm"
include "cmpt.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "wtru.mm"
include "cr.mm"
include "wf.mm"
include "cdr.mm"
include "wcel.mm"
include "cchr.mm"
include "cc0.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "resubdrg.mm"
include "simpri.mm"
include "crg.mm"
include "drngring.mm"
include "cz.mm"
include "czrh.mm"
include "wf1.mm"
include "wss.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of1.mm"
include "ax-mp.mm"
include "zssre.mm"
include "f1ss.mm"
include "mp2an.mm"
include "wb.mm"
include "zrhre.mm"
include "f1eq1.mm"
include "mpbir.mm"
include "rebase.mm"
include "eqid.mm"
include "re0g.mm"
include "zrhchr.mm"
include "mpbiri.mm"
include "mp2b.mm"
include "cdvr.mm"
include "qqhf.mm"
include "a1i.mm"
include "feqmptd.mm"
include "trud.mm"
include "cnumer.mm"
include "cdenom.mm"
include "co.mm"
include "cdiv.mm"
include "qqhvval.mm"
include "mpanl12.mm"
include "wne.mm"
include "f1f.mm"
include "qnumcl.mm"
include "ffvelrnd.mm"
include "qdencl.mm"
include "nnzd.mm"
include "wa.mm"
include "anim1i.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "zrhf1ker.mm"
include "mpbi.mm"
include "eleq2i.mm"
include "wfn.mm"
include "ffn.mm"
include "fniniseg.mm"
include "fvex.mm"
include "elsn.mm"
include "3bitr3ri.mm"
include "sylibr.mm"
include "nnne0d.mm"
include "adantr.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "redvr.mm"
include "syl3anc.mm"
include "fveq1i.mm"
include "fvresi.mm"
include "syl5eq.mm"
include "syl.mm"
include "oveq12d.mm"
include "qeqnumdivden.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"
include "mpteq2ia.mm"
include "mptresid.mm"
include "3eqtri.mm"

theorem qqhre
  let vq: setvar q


  assert |- ( QQHom ` RRfld ) = ( _I |` QQ )

  proof
    crefld
    cqqh
    cfv
    #
    vq
    cq
    vq
    cv
    #
    @0
    cfv
    #
    cmpt
    #
    vq
    cq
    @1
    cmpt
    cid
    cq
    cres
    @0
    @3
    wceq
    wtru
    vq
    cq
    cr
    @0
    cq
    cr
    @0
    wf
    #
    wtru
    crefld
    cdr
    wcel
    #
    crefld
    cchr
    cfv
    cc0
    wceq
    #
    @4
    cr
    ccnfld
    csubrg
    cfv
    wcel
    @5
    resubdrg
    simpri
    #
    @5
    crefld
    crg
    wcel
    #
    @6
    @7
    crefld
    drngring
    #
    @8
    @6
    cz
    cr
    crefld
    czrh
    cfv
    #
    wf1
    #
    @11
    cz
    cr
    cid
    cz
    cres
    #
    wf1
    #
    cz
    cz
    @12
    wf1
    #
    cz
    cr
    wss
    @13
    cz
    cz
    @12
    wf1o
    @14
    cz
    f1oi
    cz
    cz
    @12
    f1of1
    ax-mp
    zssre
    cz
    cz
    cr
    @12
    f1ss
    mp2an
    @10
    @12
    wceq
    @11
    @13
    wb
    zrhre
    cz
    cr
    @10
    @12
    f1eq1
    ax-mp
    mpbir
    #
    cr
    crefld
    @10
    cc0
    rebase
    @10
    eqid
    #
    re0g
    zrhchr
    mpbiri
    mp2b
    #
    cr
    crefld
    cdvr
    cfv
    #
    crefld
    @10
    rebase
    @18
    eqid
    #
    @16
    qqhf
    mp2an
    a1i
    feqmptd
    trud
    vq
    cq
    @2
    @1
    @1
    cq
    wcel
    #
    @2
    @1
    cnumer
    cfv
    #
    @10
    cfv
    #
    @1
    cdenom
    cfv
    #
    @10
    cfv
    #
    @18
    co
    #
    @22
    @24
    cdiv
    co
    #
    @1
    @5
    @6
    @20
    @2
    @25
    wceq
    @7
    @17
    cr
    @18
    @1
    crefld
    @10
    rebase
    @19
    @16
    qqhvval
    mpanl12
    @20
    @22
    cr
    wcel
    @24
    cr
    wcel
    @24
    cc0
    wne
    @25
    @26
    wceq
    @20
    cz
    cr
    @21
    @10
    cz
    cr
    @10
    wf
    #
    @20
    @11
    @27
    @15
    cz
    cr
    @10
    f1f
    ax-mp
    #
    a1i
    #
    @1
    qnumcl
    #
    ffvelrnd
    @20
    cz
    cr
    @23
    @10
    @29
    @20
    @23
    @1
    qdencl
    #
    nnzd
    #
    ffvelrnd
    @20
    @24
    cc0
    @20
    @24
    cc0
    wceq
    #
    @23
    cc0
    wceq
    #
    @20
    @33
    wa
    #
    @23
    cz
    wcel
    #
    @33
    wa
    #
    @34
    @20
    @36
    @33
    @32
    anim1i
    @23
    @10
    ccnv
    cc0
    csn
    #
    cima
    #
    wcel
    #
    @23
    @38
    wcel
    @37
    @34
    @39
    @38
    @23
    @11
    @39
    @38
    wceq
    #
    @15
    @5
    @8
    @11
    @41
    wb
    @7
    @9
    cr
    crefld
    @10
    cc0
    rebase
    @16
    re0g
    zrhf1ker
    mp2b
    mpbi
    eleq2i
    @27
    @10
    cz
    wfn
    @40
    @37
    wb
    @28
    cz
    cr
    @10
    ffn
    cz
    cc0
    @23
    @10
    fniniseg
    mp2b
    @23
    cc0
    @1
    cdenom
    fvex
    elsn
    3bitr3ri
    sylibr
    @35
    @23
    cc0
    @20
    @23
    cc0
    wne
    @33
    @20
    @23
    @31
    nnne0d
    adantr
    neneqd
    pm2.65da
    neqned
    @22
    @24
    redvr
    syl3anc
    @20
    @26
    @21
    @23
    cdiv
    co
    @1
    @20
    @22
    @21
    @24
    @23
    cdiv
    @20
    @21
    cz
    wcel
    #
    @22
    @21
    wceq
    @30
    @42
    @22
    @21
    @12
    cfv
    @21
    @21
    @10
    @12
    zrhre
    fveq1i
    cz
    @21
    fvresi
    syl5eq
    syl
    @20
    @36
    @24
    @23
    wceq
    @32
    @36
    @24
    @23
    @12
    cfv
    @23
    @23
    @10
    @12
    zrhre
    fveq1i
    cz
    @23
    fvresi
    syl5eq
    syl
    oveq12d
    @1
    qeqnumdivden
    eqtr4d
    3eqtrd
    mpteq2ia
    vq
    cq
    mptresid
    3eqtri
end
