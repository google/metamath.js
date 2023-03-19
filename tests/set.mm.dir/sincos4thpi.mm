include "cpi.mm"
include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "c1.mm"
include "c2.mm"
include "csqrt.mm"
include "wceq.mm"
include "ccos.mm"
include "cmul.mm"
include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "halfcn.mm"
include "ax-1cn.mm"
include "2halves.mm"
include "ax-mp.mm"
include "sincosq1eq.mm"
include "mp3an.mm"
include "oveq2i.mm"
include "2cn.mm"
include "pire.mm"
include "recni.mm"
include "2ne0.mm"
include "divmuldivi.mm"
include "mulid2i.mm"
include "2t2e4.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "recidi.mm"
include "oveq1i.mm"
include "2re.mm"
include "redivcli.mm"
include "mulassi.mm"
include "3eqtr3i.mm"
include "mulcli.mm"
include "sin2t.mm"
include "sinhalfpi.mm"
include "cr.mm"
include "4re.mm"
include "4ne0.mm"
include "resincl.mm"
include "remulcli.mm"
include "0le2.mm"
include "msqge0i.mm"
include "sqrtmulii.mm"
include "sqrt1.mm"
include "3eqtr3ri.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "wb.mm"
include "cle.mm"
include "wbr.mm"
include "sqrtcli.mm"
include "sqrt2re.mm"
include "sqrt00.mm"
include "mp2an.mm"
include "necon3bii.mm"
include "mpbir.mm"
include "pm3.2i.mm"
include "divmul2.mm"
include "0re.mm"
include "cioc.mm"
include "clt.mm"
include "pipos.mm"
include "4pos.mm"
include "divgt0ii.mm"
include "1re.mm"
include "pigt2lt4.mm"
include "simpri.mm"
include "ltdiv1ii.mm"
include "mpbi.mm"
include "dividi.mm"
include "breqtri.mm"
include "ltleii.mm"
include "cxr.mm"
include "w3a.mm"
include "0xr.mm"
include "elioc2.mm"
include "mpbir3an.mm"
include "sin01gt0.mm"
include "sqrtmsqi.mm"
include "eqtr2i.mm"

theorem sincos4thpi



  assert |- ( ( sin ` ( _pi / 4 ) ) = ( 1 / ( sqrt ` 2 ) ) /\ ( cos ` ( _pi / 4 ) ) = ( 1 / ( sqrt ` 2 ) ) )

  proof
    cpi
    c4
    cdiv
    co
    #
    csin
    cfv
    #
    c1
    c2
    csqrt
    cfv
    #
    cdiv
    co
    #
    wceq
    @0
    ccos
    cfv
    #
    @3
    wceq
    @3
    @1
    @1
    cmul
    co
    #
    csqrt
    cfv
    #
    @1
    @3
    @6
    wceq
    #
    c1
    @2
    @6
    cmul
    co
    #
    wceq
    #
    c2
    @5
    cmul
    co
    #
    csqrt
    cfv
    c1
    csqrt
    cfv
    @8
    c1
    @10
    c1
    csqrt
    c2
    c1
    c2
    cdiv
    co
    #
    cpi
    c2
    cdiv
    co
    #
    cmul
    co
    #
    csin
    cfv
    #
    @14
    cmul
    co
    #
    cmul
    co
    c2
    @14
    @13
    ccos
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    @10
    c1
    @15
    @17
    c2
    cmul
    @14
    @16
    @14
    cmul
    @11
    cc
    wcel
    #
    @19
    @11
    @11
    caddc
    co
    c1
    wceq
    #
    @14
    @16
    wceq
    halfcn
    halfcn
    c1
    cc
    wcel
    #
    @20
    ax-1cn
    c1
    2halves
    ax-mp
    @11
    @11
    sincosq1eq
    mp3an
    #
    oveq2i
    oveq2i
    @15
    @5
    c2
    cmul
    @14
    @1
    @14
    @1
    cmul
    @13
    @0
    csin
    @13
    c1
    cpi
    cmul
    co
    #
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    @0
    c1
    c2
    cpi
    c2
    ax-1cn
    2cn
    cpi
    pire
    recni
    #
    2cn
    2ne0
    2ne0
    divmuldivi
    @23
    cpi
    @24
    c4
    cdiv
    cpi
    @25
    mulid2i
    2t2e4
    oveq12i
    eqtri
    #
    fveq2i
    #
    @27
    oveq12i
    oveq2i
    c2
    @13
    cmul
    co
    #
    csin
    cfv
    #
    @12
    csin
    cfv
    @18
    c1
    @28
    @12
    csin
    c2
    @11
    cmul
    co
    #
    @12
    cmul
    co
    c1
    @12
    cmul
    co
    @28
    @12
    @30
    c1
    @12
    cmul
    c2
    2cn
    2ne0
    recidi
    oveq1i
    c2
    @11
    @12
    2cn
    halfcn
    @12
    cpi
    c2
    pire
    2re
    2ne0
    redivcli
    recni
    #
    mulassi
    @12
    @31
    mulid2i
    3eqtr3i
    fveq2i
    @13
    cc
    wcel
    @29
    @18
    wceq
    @11
    @12
    halfcn
    @31
    mulcli
    @13
    sin2t
    ax-mp
    sinhalfpi
    3eqtr3i
    3eqtr3i
    fveq2i
    c2
    @5
    2re
    @1
    @1
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    cpi
    c4
    pire
    4re
    4ne0
    redivcli
    #
    @0
    resincl
    ax-mp
    #
    @34
    remulcli
    #
    0le2
    @1
    @34
    msqge0i
    #
    sqrtmulii
    sqrt1
    3eqtr3ri
    @21
    @6
    cc
    wcel
    @2
    cc
    wcel
    #
    @2
    cc0
    wne
    #
    wa
    @7
    @9
    wb
    ax-1cn
    @6
    cc0
    @5
    cle
    wbr
    @6
    cr
    wcel
    @36
    @5
    @35
    sqrtcli
    ax-mp
    recni
    @37
    @38
    @2
    sqrt2re
    recni
    @38
    c2
    cc0
    wne
    2ne0
    @2
    cc0
    c2
    cc0
    c2
    cr
    wcel
    cc0
    c2
    cle
    wbr
    @2
    cc0
    wceq
    c2
    cc0
    wceq
    wb
    2re
    0le2
    c2
    sqrt00
    mp2an
    necon3bii
    mpbir
    pm3.2i
    c1
    @6
    @2
    divmul2
    mp3an
    mpbir
    #
    cc0
    @1
    cle
    wbr
    @6
    @1
    wceq
    cc0
    @1
    0re
    @34
    @0
    cc0
    c1
    cioc
    co
    wcel
    #
    cc0
    @1
    clt
    wbr
    @40
    @32
    cc0
    @0
    clt
    wbr
    #
    @0
    c1
    cle
    wbr
    #
    @33
    cpi
    c4
    pire
    4re
    pipos
    4pos
    divgt0ii
    @0
    c1
    @33
    1re
    @0
    c4
    c4
    cdiv
    co
    #
    c1
    clt
    cpi
    c4
    clt
    wbr
    #
    @0
    @43
    clt
    wbr
    c2
    cpi
    clt
    wbr
    @44
    pigt2lt4
    simpri
    cpi
    c4
    c4
    pire
    4re
    4re
    4pos
    ltdiv1ii
    mpbi
    c4
    c4
    4re
    recni
    4ne0
    dividi
    breqtri
    ltleii
    cc0
    cxr
    wcel
    c1
    cr
    wcel
    @40
    @32
    @41
    @42
    w3a
    wb
    0xr
    1re
    cc0
    c1
    @0
    elioc2
    mp2an
    mpbir3an
    @0
    sin01gt0
    ax-mp
    ltleii
    @1
    @34
    sqrtmsqi
    ax-mp
    #
    eqtr2i
    @3
    @1
    @4
    @3
    @6
    @1
    @39
    @45
    eqtri
    @14
    @16
    @1
    @4
    @22
    @27
    @13
    @0
    ccos
    @26
    fveq2i
    3eqtr3i
    eqtr2i
    pm3.2i
end
