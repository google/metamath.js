include "cr.mm"
include "casin.mm"
include "c1.mm"
include "cneg.mm"
include "cioo.mm"
include "co.mm"
include "cres.mm"
include "cdv.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "csqrt.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wtru.mm"
include "cc.mm"
include "wf.mm"
include "asinf.mm"
include "a1i.mm"
include "wss.mm"
include "ioossre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "feqresmpt.mm"
include "oveq2d.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cvv.mm"
include "cmnf.mm"
include "cioc.mm"
include "cpnf.mm"
include "cico.mm"
include "cun.mm"
include "cdif.mm"
include "eqid.mm"
include "cpr.mm"
include "wcel.mm"
include "reelprrecn.mm"
include "ccld.mm"
include "crest.mm"
include "recld2.mm"
include "crn.mm"
include "ctg.mm"
include "neg1rr.mm"
include "iocmnfcld.mm"
include "ax-mp.mm"
include "1re.mm"
include "icopnfcld.mm"
include "uncld.mm"
include "mp2an.mm"
include "tgioo2.mm"
include "fveq2i.mm"
include "eleqtri.mm"
include "restcldr.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "cldopn.mm"
include "mp1i.mm"
include "cin.mm"
include "incom.mm"
include "asindmre.mm"
include "eqtri.mm"
include "eldifi.mm"
include "asincl.mm"
include "syl.mm"
include "adantl.mm"
include "wa.mm"
include "ovexd.mm"
include "dvasin.mm"
include "difssd.mm"
include "syl5reqr.mm"
include "dvmptres3.mm"
include "eqtrd.mm"
include "trud.mm"

theorem dvreasin
  let vx: setvar x


  assert |- ( RR _D ( arcsin |` ( -u 1 (,) 1 ) ) ) = ( x e. ( -u 1 (,) 1 ) |-> ( 1 / ( sqrt ` ( 1 - ( x ^ 2 ) ) ) ) )

  proof
    cr
    casin
    c1
    cneg
    #
    c1
    cioo
    co
    #
    cres
    #
    cdv
    co
    #
    vx
    @1
    c1
    c1
    vx
    cv
    #
    c2
    cexp
    co
    cmin
    co
    csqrt
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    wceq
    wtru
    @3
    cr
    vx
    @1
    @4
    casin
    cfv
    #
    cmpt
    #
    cdv
    co
    @7
    wtru
    @2
    @9
    cr
    cdv
    wtru
    vx
    cc
    cc
    @1
    casin
    cc
    cc
    casin
    wf
    wtru
    asinf
    a1i
    #
    @1
    cc
    wss
    wtru
    @1
    cr
    cc
    @0
    c1
    ioossre
    ax-resscn
    sstri
    a1i
    feqresmpt
    oveq2d
    wtru
    vx
    @8
    @6
    cr
    ccnfld
    ctopn
    cfv
    #
    cvv
    cc
    cmnf
    @0
    cioc
    co
    #
    c1
    cpnf
    cico
    co
    #
    cun
    #
    cdif
    #
    @1
    @11
    eqid
    #
    cr
    cr
    cc
    cpr
    wcel
    wtru
    reelprrecn
    a1i
    @14
    @11
    ccld
    cfv
    #
    wcel
    #
    @15
    @11
    wcel
    wtru
    cr
    @17
    wcel
    @14
    @11
    cr
    crest
    co
    #
    ccld
    cfv
    #
    wcel
    @18
    @11
    @16
    recld2
    @14
    cioo
    crn
    ctg
    cfv
    #
    ccld
    cfv
    #
    @20
    @12
    @22
    wcel
    #
    @13
    @22
    wcel
    #
    @14
    @22
    wcel
    @0
    cr
    wcel
    @23
    neg1rr
    @0
    iocmnfcld
    ax-mp
    c1
    cr
    wcel
    @24
    1re
    c1
    icopnfcld
    ax-mp
    @12
    @13
    @21
    uncld
    mp2an
    @21
    @19
    ccld
    @11
    @16
    tgioo2
    fveq2i
    eleqtri
    cr
    @14
    @11
    restcldr
    mp2an
    @14
    @11
    cc
    cc
    @11
    @11
    @16
    cnfldtopon
    toponunii
    cldopn
    mp1i
    cr
    @15
    cin
    #
    @1
    wceq
    wtru
    @25
    @15
    cr
    cin
    @1
    cr
    @15
    incom
    @15
    @15
    eqid
    #
    asindmre
    eqtri
    a1i
    @4
    @15
    wcel
    #
    @8
    cc
    wcel
    #
    wtru
    @27
    @4
    cc
    wcel
    @28
    @4
    cc
    @14
    eldifi
    @4
    asincl
    syl
    adantl
    wtru
    @27
    wa
    c1
    @5
    cdiv
    ovexd
    wtru
    vx
    @15
    @6
    cmpt
    cc
    casin
    @15
    cres
    #
    cdv
    co
    cc
    vx
    @15
    @8
    cmpt
    #
    cdv
    co
    vx
    @15
    @26
    dvasin
    wtru
    @29
    @30
    cc
    cdv
    wtru
    vx
    cc
    cc
    @15
    casin
    @10
    wtru
    cc
    @14
    difssd
    feqresmpt
    oveq2d
    syl5reqr
    dvmptres3
    eqtrd
    trud
end
