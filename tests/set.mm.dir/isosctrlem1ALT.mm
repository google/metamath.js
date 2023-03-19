include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wn.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "clog.mm"
include "cim.mm"
include "cpi.mm"
include "cr.mm"
include "wa.mm"
include "ax-1cn.mm"
include "a1i.mm"
include "id.mm"
include "subcld.mm"
include "adantr.mm"
include "cc0.mm"
include "wne.mm"
include "wi.mm"
include "subeq0.mm"
include "biimpd.mm"
include "idiALT.mm"
include "sylancr.mm"
include "con3d.mm"
include "df-ne.mm"
include "biimpri.mm"
include "syl6.mm"
include "imp.mm"
include "logcld.mm"
include "imcld.mm"
include "3adant2.mm"
include "c2.mm"
include "cdiv.mm"
include "pire.mm"
include "2re.mm"
include "2ne0.mm"
include "redivcli.mm"
include "cneg.mm"
include "cxr.mm"
include "cicc.mm"
include "cle.mm"
include "wbr.mm"
include "neghalfpirx.mm"
include "rexri.mm"
include "cre.mm"
include "recld.mm"
include "recnd.mm"
include "subidd.mm"
include "1re.mm"
include "ax-mp.mm"
include "releabsd.mm"
include "adantl.mm"
include "breqtrd.mm"
include "lesub1.mm"
include "3impcombi.mm"
include "mp3an2ani.mm"
include "eqbrtrrd.mm"
include "wtru.mm"
include "rered.mm"
include "trud.mm"
include "oveq1.mm"
include "eqcomd.mm"
include "resub.mm"
include "syl5eq.mm"
include "argrege0.mm"
include "3coml.mm"
include "3com13.mm"
include "eel12131.mm"
include "iccleub.mm"
include "mp3an12i.mm"
include "clt.mm"
include "crp.mm"
include "pipos.mm"
include "elrpii.mm"
include "rphalflt.mm"
include "lelttrd.mm"
include "ltned.mm"

theorem isosctrlem1ALT
  let cA: class A


  assert |- ( ( A e. CC /\ ( abs ` A ) = 1 /\ -. 1 = A ) -> ( Im ` ( log ` ( 1 - A ) ) ) =/= _pi )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    #
    c1
    wceq
    #
    c1
    cA
    wceq
    #
    wn
    #
    w3a
    #
    c1
    cA
    cmin
    co
    #
    clog
    cfv
    #
    cim
    cfv
    #
    cpi
    @0
    @4
    @8
    cr
    wcel
    @2
    @0
    @4
    wa
    #
    @7
    @9
    @6
    @0
    @6
    cc
    wcel
    #
    @4
    @0
    c1
    cA
    c1
    cc
    wcel
    #
    @0
    ax-1cn
    a1i
    @0
    id
    #
    subcld
    #
    adantr
    @0
    @4
    @6
    cc0
    wne
    #
    @0
    @4
    @6
    cc0
    wceq
    #
    wn
    #
    @14
    @0
    @15
    @3
    @0
    @11
    @0
    @15
    @3
    wi
    #
    ax-1cn
    @12
    @11
    @0
    wa
    #
    @17
    wi
    @18
    @15
    @3
    c1
    cA
    subeq0
    biimpd
    idiALT
    sylancr
    con3d
    @14
    @16
    @6
    cc0
    df-ne
    biimpri
    syl6
    imp
    #
    logcld
    imcld
    3adant2
    #
    @5
    @8
    cpi
    c2
    cdiv
    co
    #
    cpi
    @20
    @21
    cr
    wcel
    @5
    cpi
    c2
    pire
    2re
    2ne0
    redivcli
    #
    a1i
    cpi
    cr
    wcel
    @5
    pire
    a1i
    @21
    cneg
    #
    cxr
    wcel
    @21
    cxr
    wcel
    @5
    @8
    @23
    @21
    cicc
    co
    wcel
    #
    @8
    @21
    cle
    wbr
    neghalfpirx
    @21
    @22
    rexri
    @0
    @10
    @2
    cc0
    @6
    cre
    cfv
    #
    cle
    wbr
    #
    @4
    @14
    @24
    @13
    @0
    @2
    wa
    #
    cc0
    c1
    cA
    cre
    cfv
    #
    cmin
    co
    #
    @25
    cle
    @27
    @28
    @28
    cmin
    co
    #
    cc0
    @29
    cle
    @0
    @30
    cc0
    wceq
    @2
    @0
    @28
    @0
    @28
    @0
    cA
    @12
    recld
    #
    recnd
    subidd
    adantr
    c1
    cr
    wcel
    #
    @0
    @28
    cr
    wcel
    #
    @2
    @28
    c1
    cle
    wbr
    #
    @30
    @29
    cle
    wbr
    #
    @11
    @32
    ax-1cn
    @32
    @11
    1re
    a1i
    ax-mp
    #
    @31
    @27
    @28
    @1
    c1
    cle
    @0
    @28
    @1
    cle
    wbr
    @2
    @0
    cA
    @12
    releabsd
    adantr
    @2
    @2
    @0
    @2
    id
    adantl
    breqtrd
    @32
    @33
    @34
    w3a
    @35
    wi
    @33
    @32
    @34
    @35
    @28
    c1
    @28
    lesub1
    3impcombi
    idiALT
    mp3an2ani
    eqbrtrrd
    @0
    @29
    @25
    wceq
    @2
    @0
    @29
    c1
    cre
    cfv
    #
    @28
    cmin
    co
    #
    @25
    @37
    c1
    wceq
    #
    @29
    @38
    wceq
    @39
    wtru
    c1
    @32
    wtru
    @36
    a1i
    rered
    trud
    @39
    @38
    @29
    @37
    c1
    @28
    cmin
    oveq1
    eqcomd
    ax-mp
    @0
    @11
    @0
    @38
    @25
    wceq
    #
    ax-1cn
    @12
    @18
    @40
    wi
    @18
    @25
    @38
    c1
    cA
    resub
    eqcomd
    idiALT
    sylancr
    syl5eq
    adantr
    breqtrd
    @19
    @14
    @26
    @10
    @24
    @10
    @14
    @26
    @24
    @6
    argrege0
    3coml
    3com13
    eel12131
    @23
    @21
    @8
    iccleub
    mp3an12i
    @21
    cpi
    clt
    wbr
    #
    @5
    cpi
    crp
    wcel
    @41
    cpi
    pire
    pipos
    elrpii
    cpi
    rphalflt
    ax-mp
    a1i
    lelttrd
    ltned
end
