include "cc.mm"
include "clog.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "cdif.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cnt.mm"
include "wss.mm"
include "wf.mm"
include "wceq.mm"
include "ssid.mm"
include "csn.mm"
include "crn.mm"
include "wf1o.mm"
include "logf1o.mm"
include "f1of.mm"
include "ax-mp.mm"
include "logrncn.mm"
include "ssriv.mm"
include "fss.mm"
include "mp2an.mm"
include "eqid.mm"
include "logdmss.mm"
include "fssres.mm"
include "difss.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cxmt.mm"
include "wcel.mm"
include "cxr.mm"
include "cnxmet.mm"
include "ax-1cn.mm"
include "crp.mm"
include "1rp.mm"
include "rpxr.mm"
include "blssm.mm"
include "mp3an.mm"
include "eqsstri.mm"
include "crest.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "eqcomi.mm"
include "dvres.mm"
include "mp4an.mm"
include "dvlog2lem.mm"
include "resabs1.mm"
include "oveq2i.mm"
include "dvlog.mm"
include "cnfldtopn.mm"
include "blopn.mm"
include "eqeltri.mm"
include "isopn3i.mm"
include "reseq12i.mm"
include "3eqtr3i.mm"
include "resmpt.mm"
include "eqtri.mm"

theorem dvlog2
  let vx: setvar x
  let cS: class S
  assume dvlog2.s: |- S = ( 1 ( ball ` ( abs o. - ) ) 1 )

  disjoint S x
  assert |- ( CC _D ( log |` S ) ) = ( x e. S |-> ( 1 / x ) )

  proof
    cc
    clog
    cS
    cres
    #
    cdv
    co
    #
    vx
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    #
    c1
    vx
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    cS
    cres
    #
    vx
    cS
    @5
    cmpt
    #
    cc
    clog
    @3
    cres
    #
    cS
    cres
    #
    cdv
    co
    #
    cc
    @9
    cdv
    co
    #
    cS
    ccnfld
    ctopn
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @1
    @7
    cc
    cc
    wss
    @3
    cc
    @9
    wf
    #
    @3
    cc
    wss
    cS
    cc
    wss
    @11
    @15
    wceq
    cc
    ssid
    cc
    cc0
    csn
    cdif
    #
    cc
    clog
    wf
    #
    @3
    @17
    wss
    @16
    @17
    clog
    crn
    #
    clog
    wf
    #
    @19
    cc
    wss
    @18
    @17
    @19
    clog
    wf1o
    @20
    logf1o
    @17
    @19
    clog
    f1of
    ax-mp
    vx
    @19
    cc
    @4
    logrncn
    ssriv
    @17
    @19
    cc
    clog
    fss
    mp2an
    @3
    @3
    eqid
    #
    logdmss
    @17
    cc
    @3
    clog
    fssres
    mp2an
    cc
    @2
    difss
    cS
    c1
    c1
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    cc
    dvlog2.s
    @22
    cc
    cxmt
    cfv
    wcel
    #
    c1
    cc
    wcel
    #
    c1
    cxr
    wcel
    #
    @23
    cc
    wss
    cnxmet
    ax-1cn
    c1
    crp
    wcel
    @26
    1rp
    c1
    rpxr
    ax-mp
    #
    @22
    c1
    c1
    cc
    blssm
    mp3an
    eqsstri
    @3
    cS
    cc
    @13
    @9
    @13
    @13
    eqid
    #
    @13
    cc
    crest
    co
    #
    @13
    @13
    ctop
    wcel
    #
    @29
    @13
    wceq
    @13
    @28
    cnfldtop
    #
    @13
    ctop
    cc
    cc
    @13
    @13
    @28
    cnfldtopon
    toponunii
    restid
    ax-mp
    eqcomi
    dvres
    mp4an
    @10
    @0
    cc
    cdv
    cS
    @3
    wss
    #
    @10
    @0
    wceq
    cS
    dvlog2.s
    dvlog2lem
    #
    clog
    cS
    @3
    resabs1
    ax-mp
    oveq2i
    @12
    @6
    @14
    cS
    vx
    @3
    @21
    dvlog
    @30
    cS
    @13
    wcel
    @14
    cS
    wceq
    @31
    cS
    @23
    @13
    dvlog2.s
    @24
    @25
    @26
    @23
    @13
    wcel
    cnxmet
    ax-1cn
    @27
    @22
    c1
    c1
    @13
    cc
    @13
    @28
    cnfldtopn
    blopn
    mp3an
    eqeltri
    cS
    @13
    isopn3i
    mp2an
    reseq12i
    3eqtr3i
    @32
    @7
    @8
    wceq
    @33
    vx
    @3
    cS
    @5
    resmpt
    ax-mp
    eqtri
end
