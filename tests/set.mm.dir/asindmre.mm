include "cc.mm"
include "cmnf.mm"
include "c1.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "cpnf.mm"
include "cico.mm"
include "cun.mm"
include "cdif.mm"
include "cr.mm"
include "cin.mm"
include "cioo.mm"
include "un12.mm"
include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "neg1rr.mm"
include "rexri.mm"
include "1re.mm"
include "pnfxr.mm"
include "3pm3.2i.mm"
include "cc0.mm"
include "neg1lt0.mm"
include "0lt1.mm"
include "0re.mm"
include "lttri.mm"
include "mp2an.mm"
include "ltpnf.mm"
include "ax-mp.mm"
include "pm3.2i.mm"
include "cle.mm"
include "df-ioo.mm"
include "df-ico.mm"
include "cv.mm"
include "xrlenlt.mm"
include "xrlttr.mm"
include "xrltletr.mm"
include "ixxun.mm"
include "uneq2i.mm"
include "mnfxr.mm"
include "mnflt.mm"
include "jca.mm"
include "df-ioc.mm"
include "xrltnle.mm"
include "xrlelttr.mm"
include "eqtri.mm"
include "ioomax.mm"
include "3eqtri.mm"
include "difeq1i.mm"
include "difun2.mm"
include "wss.mm"
include "ax-resscn.mm"
include "difin2.mm"
include "3eqtr3ri.mm"
include "ineq1i.mm"
include "c0.mm"
include "incom.mm"
include "ixxdisj.mm"
include "mp3an.mm"
include "un00.mm"
include "indi.mm"
include "eqeq1i.mm"
include "disj3.mm"
include "3bitr2i.mm"
include "mpbi.mm"
include "3eqtr4i.mm"

theorem asindmre
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume dvasin.d: |- D = ( CC \ ( ( -oo (,] -u 1 ) u. ( 1 [,) +oo ) ) )


  assert |- ( D i^i RR ) = ( -u 1 (,) 1 )

  proof
    cc
    cmnf
    c1
    cneg
    #
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
    cr
    cin
    #
    @0
    c1
    cioo
    co
    #
    @3
    cdif
    #
    cD
    cr
    cin
    @6
    @6
    @3
    cun
    #
    @3
    cdif
    cr
    @3
    cdif
    #
    @7
    @5
    @8
    cr
    @3
    @8
    @1
    @6
    @2
    cun
    #
    cun
    #
    cmnf
    cpnf
    cioo
    co
    #
    cr
    @6
    @1
    @2
    un12
    @11
    @1
    @0
    cpnf
    cioo
    co
    #
    cun
    #
    @12
    @10
    @13
    @1
    @0
    cxr
    wcel
    #
    c1
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    w3a
    @0
    c1
    clt
    wbr
    #
    c1
    cpnf
    clt
    wbr
    #
    wa
    @10
    @13
    wceq
    @15
    @16
    @17
    @0
    neg1rr
    rexri
    #
    c1
    1re
    rexri
    #
    pnfxr
    3pm3.2i
    @18
    @19
    @0
    cc0
    clt
    wbr
    cc0
    c1
    clt
    wbr
    @18
    neg1lt0
    0lt1
    @0
    cc0
    c1
    neg1rr
    0re
    1re
    lttri
    mp2an
    c1
    cr
    wcel
    @19
    1re
    c1
    ltpnf
    ax-mp
    pm3.2i
    vx
    vy
    vz
    vw
    @0
    c1
    cpnf
    cico
    cioo
    clt
    clt
    cle
    clt
    cioo
    clt
    clt
    vx
    vy
    vz
    df-ioo
    #
    vx
    vy
    vz
    df-ico
    #
    c1
    vw
    cv
    #
    xrlenlt
    #
    @22
    @24
    c1
    cpnf
    xrlttr
    @0
    c1
    @24
    xrltletr
    ixxun
    mp2an
    uneq2i
    cmnf
    cxr
    wcel
    #
    @15
    @17
    w3a
    cmnf
    @0
    clt
    wbr
    #
    @0
    cpnf
    clt
    wbr
    #
    wa
    #
    @14
    @12
    wceq
    @26
    @15
    @17
    mnfxr
    @20
    pnfxr
    3pm3.2i
    @0
    cr
    wcel
    #
    @29
    neg1rr
    @30
    @27
    @28
    @0
    mnflt
    @0
    ltpnf
    jca
    ax-mp
    vx
    vy
    vz
    vw
    cmnf
    @0
    cpnf
    cioo
    cioo
    clt
    cle
    clt
    clt
    cioc
    clt
    clt
    vx
    vy
    vz
    df-ioc
    #
    @22
    @0
    @24
    xrltnle
    #
    @22
    @24
    @0
    cpnf
    xrlelttr
    cmnf
    @0
    @24
    xrlttr
    ixxun
    mp2an
    eqtri
    ioomax
    3eqtri
    difeq1i
    @6
    @3
    difun2
    cr
    cc
    wss
    @9
    @5
    wceq
    ax-resscn
    cr
    @3
    cc
    difin2
    ax-mp
    3eqtr3ri
    cD
    @4
    cr
    dvasin.d
    ineq1i
    @6
    @1
    cin
    #
    c0
    wceq
    #
    @6
    @2
    cin
    #
    c0
    wceq
    #
    wa
    #
    @6
    @7
    wceq
    #
    @34
    @36
    @33
    @1
    @6
    cin
    #
    c0
    @6
    @1
    incom
    @26
    @15
    @16
    @39
    c0
    wceq
    mnfxr
    @20
    @21
    vx
    vy
    vz
    vw
    cmnf
    @0
    c1
    cioo
    clt
    cle
    clt
    clt
    cioc
    @31
    @22
    @32
    ixxdisj
    mp3an
    eqtri
    @15
    @16
    @17
    @36
    @20
    @21
    pnfxr
    vx
    vy
    vz
    vw
    @0
    c1
    cpnf
    cico
    clt
    clt
    cle
    clt
    cioo
    @22
    @23
    @25
    ixxdisj
    mp3an
    pm3.2i
    @37
    @33
    @35
    cun
    #
    c0
    wceq
    @6
    @3
    cin
    #
    c0
    wceq
    @38
    @33
    @35
    un00
    @41
    @40
    c0
    @6
    @1
    @2
    indi
    eqeq1i
    @6
    @3
    disj3
    3bitr2i
    mpbi
    3eqtr4i
end
