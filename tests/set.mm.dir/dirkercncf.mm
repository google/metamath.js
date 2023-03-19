include "cn.mm"
include "wcel.mm"
include "cfv.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ccn.mm"
include "co.mm"
include "cr.mm"
include "ccncf.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "wral.mm"
include "dirkerf.mm"
include "wa.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cc.mm"
include "climc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "fssd.mm"
include "ad2antrr.mm"
include "cmin.mm"
include "caddc.mm"
include "c1.mm"
include "cdiv.mm"
include "csin.mm"
include "cmpt.mm"
include "cif.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "eqid.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "dirkercncflem3.mm"
include "wb.mm"
include "jctl.mm"
include "ad2antlr.mm"
include "tgioo2.mm"
include "cnplimc.mm"
include "syl.mm"
include "mpbir2and.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "retopon.mm"
include "toponunii.mm"
include "cnfldtopon.mm"
include "cnprest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "eqcomi.mm"
include "fveq1d.mm"
include "eleqtrd.mm"
include "wn.mm"
include "cfl.mm"
include "wne.mm"
include "neqne.mm"
include "adantl.mm"
include "dirkercncflem4.mm"
include "pm2.61dan.mm"
include "ralrimiva.mm"
include "ctopon.mm"
include "cncnp.mm"
include "mp2an.mm"
include "sylanbrc.mm"
include "cncfcn.mm"
include "syl6eleqr.mm"

theorem dirkercncf
  let vy: setvar y
  let cD: class D
  let vn: setvar n
  let cN: class N
  let vw: setvar w
  let vk: setvar k
  let vx: setvar x
  assume dirkercncf.d: |- D = ( n e. NN |-> ( y e. RR |-> if ( ( y mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. n ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( n + ( 1 / 2 ) ) x. y ) ) / ( ( 2 x. _pi ) x. ( sin ` ( y / 2 ) ) ) ) ) ) )

  disjoint D y
  disjoint N y
  disjoint n y
  disjoint D w
  disjoint w y
  disjoint N w
  disjoint n w
  disjoint k x
  assert |- ( N e. NN -> ( D ` N ) e. ( RR -cn-> RR ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cD
    cfv
    #
    cioo
    crn
    ctg
    cfv
    #
    @2
    ccn
    co
    #
    cr
    cr
    ccncf
    co
    #
    @0
    cr
    cr
    @1
    wf
    #
    @1
    vy
    cv
    #
    @2
    @2
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    vy
    cr
    wral
    #
    @1
    @3
    wcel
    #
    vy
    cD
    vn
    cN
    dirkercncf.d
    dirkerf
    #
    @0
    @9
    vy
    cr
    @0
    @6
    cr
    wcel
    #
    wa
    #
    @6
    c2
    cpi
    cmul
    co
    #
    cmo
    co
    #
    cc0
    wceq
    #
    @9
    @14
    @17
    wa
    #
    @1
    @6
    @2
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    ccnp
    co
    #
    cfv
    #
    @8
    @18
    @1
    @6
    @2
    @19
    ccnp
    co
    cfv
    wcel
    #
    @1
    @22
    wcel
    #
    @18
    @23
    cr
    cc
    @1
    wf
    #
    @6
    @1
    cfv
    @1
    @6
    climc
    co
    wcel
    #
    @0
    @25
    @13
    @17
    @0
    cr
    cr
    cc
    @1
    @12
    cr
    cc
    wss
    #
    @0
    ax-resscn
    a1i
    fssd
    ad2antrr
    @18
    vw
    @6
    cpi
    cmin
    co
    #
    @6
    cpi
    caddc
    co
    #
    cD
    vn
    vw
    @28
    @29
    cioo
    co
    #
    vn
    cv
    #
    c1
    c2
    cdiv
    co
    caddc
    co
    #
    vw
    cv
    #
    cmul
    co
    #
    csin
    cfv
    #
    @15
    @33
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cmpt
    #
    vw
    @30
    @38
    cmpt
    #
    cN
    @6
    cD
    vn
    cn
    vy
    cr
    @17
    c2
    @31
    cmul
    co
    c1
    caddc
    co
    @15
    cdiv
    co
    #
    @32
    @6
    cmul
    co
    #
    csin
    cfv
    #
    @15
    @6
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cif
    #
    cmpt
    #
    cmpt
    vn
    cn
    vw
    cr
    @33
    @15
    cmo
    co
    #
    cc0
    wceq
    #
    @42
    @39
    cif
    #
    cmpt
    #
    cmpt
    dirkercncf.d
    vn
    cn
    @50
    @54
    vy
    vw
    cr
    @49
    @53
    @6
    @33
    wceq
    #
    @17
    @52
    @48
    @39
    @42
    @55
    @16
    @51
    cc0
    @6
    @33
    @15
    cmo
    oveq1
    eqeq1d
    @55
    @44
    @35
    @47
    @38
    cdiv
    @55
    @43
    @34
    csin
    @6
    @33
    @32
    cmul
    oveq2
    fveq2d
    @55
    @46
    @37
    @15
    cmul
    @55
    @45
    @36
    csin
    @6
    @33
    c2
    cdiv
    oveq1
    fveq2d
    oveq2d
    oveq12d
    ifbieq2d
    cbvmptv
    mpteq2i
    eqtri
    #
    @28
    eqid
    @29
    eqid
    @40
    eqid
    @41
    eqid
    @0
    @13
    @17
    simpll
    @0
    @13
    @17
    simplr
    @14
    @17
    simpr
    dirkercncflem3
    @18
    @27
    @13
    wa
    #
    @23
    @25
    @26
    wa
    wb
    @13
    @57
    @0
    @17
    @13
    @27
    ax-resscn
    jctl
    ad2antlr
    cr
    @6
    @1
    @2
    @19
    @19
    eqid
    #
    @19
    @58
    tgioo2
    #
    cnplimc
    syl
    mpbir2and
    @18
    @19
    ctop
    wcel
    #
    @5
    @27
    @23
    @24
    wb
    @60
    @18
    @19
    @58
    cnfldtop
    a1i
    @0
    @5
    @13
    @17
    @12
    ad2antrr
    @27
    @18
    ax-resscn
    a1i
    cr
    @6
    @1
    @2
    @19
    cr
    cc
    cr
    @2
    retopon
    toponunii
    cc
    @19
    @19
    @58
    cnfldtopon
    toponunii
    cnprest2
    syl3anc
    mpbid
    @18
    @6
    @21
    @7
    @18
    @20
    @2
    @2
    ccnp
    @20
    @2
    wceq
    @18
    @2
    @20
    @59
    eqcomi
    a1i
    oveq2d
    fveq1d
    eleqtrd
    @14
    @17
    wn
    #
    wa
    vw
    @6
    @15
    cdiv
    co
    cfl
    cfv
    #
    @62
    c1
    caddc
    co
    #
    @62
    @15
    cmul
    co
    #
    cD
    vn
    @63
    @15
    cmul
    co
    #
    cN
    @6
    @56
    @0
    @13
    @61
    simpll
    @0
    @13
    @61
    simplr
    @61
    @16
    cc0
    wne
    @14
    @16
    cc0
    neqne
    adantl
    @62
    eqid
    @63
    eqid
    @64
    eqid
    @65
    eqid
    dirkercncflem4
    pm2.61dan
    ralrimiva
    @2
    cr
    ctopon
    cfv
    wcel
    #
    @66
    @11
    @5
    @10
    wa
    wb
    retopon
    retopon
    vy
    @1
    @2
    @2
    cr
    cr
    cncnp
    mp2an
    sylanbrc
    @27
    @27
    @4
    @3
    wceq
    ax-resscn
    ax-resscn
    cr
    cr
    @19
    @2
    @2
    @58
    @59
    @59
    cncfcn
    mp2an
    syl6eleqr
end
