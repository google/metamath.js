include "cr.mm"
include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cdif.mm"
include "wss.mm"
include "cv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "co.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "difss.mm"
include "cim.mm"
include "eldifi.mm"
include "imcld.mm"
include "recnd.mm"
include "wn.mm"
include "cc0.mm"
include "wne.mm"
include "eldifn.mm"
include "wceq.mm"
include "wb.mm"
include "reim0b.mm"
include "syl.mm"
include "necon3bbid.mm"
include "mpbid.mm"
include "absrpcld.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cxmt.mm"
include "cxr.mm"
include "cnxmet.mm"
include "a1i.mm"
include "abscld.mm"
include "rexrd.mm"
include "elbl.mm"
include "syl3anc.mm"
include "simprl.mm"
include "wi.mm"
include "cle.mm"
include "adantr.mm"
include "simpr.mm"
include "imsubd.mm"
include "reim0.mm"
include "adantl.mm"
include "oveq2d.mm"
include "subid1d.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "subcld.mm"
include "absimle.mm"
include "eqbrtrrd.mm"
include "lenltd.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "syl2anc.mm"
include "breq1d.mm"
include "mtbird.mm"
include "ex.mm"
include "con2d.mm"
include "impr.mm"
include "eldifd.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "rgen.mm"
include "cnfldtopn.mm"
include "elmopn2.mm"
include "ax-mp.mm"
include "mpbir2an.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "ax-resscn.mm"
include "cuni.mm"
include "mopnuni.mm"
include "iscld2.mm"
include "mp2an.mm"
include "mpbir.mm"

theorem recld2
  let cJ: class J
  let vn: setvar n
  let vr: setvar r
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cS: class S
  assume recld2.1: |- J = ( TopOpen ` CCfld )


  assert |- RR e. ( Clsd ` J )

  proof
    cr
    cJ
    ccld
    cfv
    wcel
    #
    cc
    cr
    cdif
    #
    cJ
    wcel
    #
    @2
    @1
    cc
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    #
    co
    #
    @1
    wss
    #
    vy
    crp
    wrex
    #
    vx
    @1
    wral
    #
    cc
    cr
    difss
    @10
    vx
    @1
    @4
    @1
    wcel
    #
    @4
    cim
    cfv
    #
    cabs
    cfv
    #
    crp
    wcel
    @4
    @14
    @7
    co
    #
    @1
    wss
    #
    @10
    @12
    @13
    @12
    @13
    @12
    @4
    @4
    cc
    cr
    eldifi
    #
    imcld
    recnd
    #
    @12
    @4
    cr
    wcel
    #
    wn
    @13
    cc0
    wne
    @4
    cc
    cr
    eldifn
    @12
    @19
    @13
    cc0
    @12
    @4
    cc
    wcel
    #
    @19
    @13
    cc0
    wceq
    wb
    @17
    @4
    reim0b
    syl
    necon3bbid
    mpbid
    absrpcld
    @12
    vy
    @15
    @1
    @12
    @5
    @15
    wcel
    #
    @5
    cc
    wcel
    #
    @4
    @5
    @6
    co
    #
    @14
    clt
    wbr
    #
    wa
    #
    @5
    @1
    wcel
    #
    @12
    @6
    cc
    cxmt
    cfv
    wcel
    #
    @20
    @14
    cxr
    wcel
    @21
    @25
    wb
    @27
    @12
    cnxmet
    a1i
    @17
    @12
    @14
    @12
    @13
    @18
    abscld
    rexrd
    @5
    @6
    @4
    @14
    cc
    elbl
    syl3anc
    @12
    @25
    @26
    @12
    @25
    wa
    @5
    cc
    cr
    @12
    @22
    @24
    simprl
    @12
    @22
    @24
    @5
    cr
    wcel
    #
    wn
    #
    @12
    @24
    @29
    wi
    @22
    @12
    @28
    @24
    @12
    @28
    @24
    wn
    @12
    @28
    wa
    #
    @24
    @4
    @5
    cmin
    co
    #
    cabs
    cfv
    #
    @14
    clt
    wbr
    #
    @30
    @14
    @32
    cle
    wbr
    @33
    wn
    @30
    @31
    cim
    cfv
    #
    cabs
    cfv
    #
    @14
    @32
    cle
    @30
    @34
    @13
    cabs
    @30
    @34
    @13
    @5
    cim
    cfv
    #
    cmin
    co
    @13
    cc0
    cmin
    co
    @13
    @30
    @4
    @5
    @12
    @20
    @28
    @17
    adantr
    #
    @30
    @5
    @12
    @28
    simpr
    recnd
    #
    imsubd
    @30
    @36
    cc0
    @13
    cmin
    @28
    @36
    cc0
    wceq
    @12
    @5
    reim0
    adantl
    oveq2d
    @30
    @13
    @12
    @13
    cc
    wcel
    @28
    @18
    adantr
    #
    subid1d
    3eqtrd
    fveq2d
    @30
    @31
    cc
    wcel
    @35
    @32
    cle
    wbr
    @30
    @4
    @5
    @37
    @38
    subcld
    #
    @31
    absimle
    syl
    eqbrtrrd
    @30
    @14
    @32
    @30
    @13
    @39
    abscld
    @30
    @31
    @40
    abscld
    lenltd
    mpbid
    @30
    @23
    @32
    @14
    clt
    @30
    @20
    @22
    @23
    @32
    wceq
    @37
    @38
    @4
    @5
    @6
    @6
    eqid
    cnmetdval
    syl2anc
    breq1d
    mtbird
    ex
    con2d
    adantr
    impr
    eldifd
    ex
    sylbid
    ssrdv
    @9
    @16
    vy
    @14
    crp
    @5
    @14
    wceq
    @8
    @15
    @1
    @5
    @14
    @4
    @7
    oveq2
    sseq1d
    rspcev
    syl2anc
    rgen
    @27
    @2
    @3
    @11
    wa
    wb
    cnxmet
    vx
    vy
    @1
    @6
    cJ
    cc
    cJ
    recld2.1
    cnfldtopn
    #
    elmopn2
    ax-mp
    mpbir2an
    cJ
    ctop
    wcel
    cr
    cc
    wss
    @0
    @2
    wb
    cJ
    recld2.1
    cnfldtop
    ax-resscn
    cr
    cJ
    cc
    @27
    cc
    cJ
    cuni
    wceq
    cnxmet
    @6
    cJ
    cc
    @41
    mopnuni
    ax-mp
    iscld2
    mp2an
    mpbir
end
