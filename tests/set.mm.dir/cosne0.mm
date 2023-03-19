include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cioo.mm"
include "wa.mm"
include "ccos.mm"
include "cmin.mm"
include "csin.mm"
include "cc0.mm"
include "wceq.mm"
include "halfpire.mm"
include "recni.mm"
include "simpl.mm"
include "nncan.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "subcl.mm"
include "coshalfpim.mm"
include "syl.mm"
include "eqtr3d.mm"
include "wne.mm"
include "cz.mm"
include "wn.mm"
include "cr.mm"
include "adantr.mm"
include "cmul.mm"
include "picn.mm"
include "a1i.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "divcan1d.mm"
include "zre.mm"
include "adantl.mm"
include "remulcl.mm"
include "sylancl.mm"
include "eqeltrrd.mm"
include "resubcl.mm"
include "rered.mm"
include "simplr.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "0zd.mm"
include "elioore.mm"
include "eliooord.mm"
include "simprd.mm"
include "wb.mm"
include "posdif.mm"
include "mpbid.mm"
include "divgt0d.mm"
include "negcli.mm"
include "negsubi.mm"
include "pidiv2halves.mm"
include "subaddrii.mm"
include "eqtri.mm"
include "simpld.mm"
include "syl5eqbr.mm"
include "ltsub23d.mm"
include "mulid1i.mm"
include "syl6breqr.mm"
include "1red.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "1e0p1.mm"
include "syl6breq.mm"
include "btwnnz.mm"
include "syl3anc.mm"
include "pm2.01da.mm"
include "sineq0.mm"
include "necon3abid.mm"
include "eqnetrd.mm"

theorem cosne0
  let cA: class A


  assert |- ( ( A e. CC /\ ( Re ` A ) e. ( -u ( _pi / 2 ) (,) ( _pi / 2 ) ) ) -> ( cos ` A ) =/= 0 )

  proof
    cA
    cc
    wcel
    #
    cA
    cre
    cfv
    #
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @2
    cioo
    co
    #
    wcel
    #
    wa
    #
    cA
    ccos
    cfv
    #
    @2
    cA
    cmin
    co
    #
    csin
    cfv
    #
    cc0
    @6
    @2
    @8
    cmin
    co
    #
    ccos
    cfv
    #
    @7
    @9
    @6
    @10
    cA
    ccos
    @6
    @2
    cc
    wcel
    #
    @0
    @10
    cA
    wceq
    #
    @2
    halfpire
    recni
    #
    @0
    @5
    simpl
    #
    @2
    cA
    nncan
    sylancr
    #
    fveq2d
    @6
    @8
    cc
    wcel
    #
    @11
    @9
    wceq
    @6
    @12
    @0
    @17
    @14
    @15
    @2
    cA
    subcl
    sylancr
    #
    @8
    coshalfpim
    syl
    eqtr3d
    @6
    @9
    cc0
    wne
    @8
    cpi
    cdiv
    co
    #
    cz
    wcel
    #
    wn
    #
    @6
    @20
    @6
    @20
    wa
    #
    cA
    @4
    wcel
    #
    @21
    @22
    @1
    cA
    @4
    @22
    cA
    @22
    @10
    cA
    cr
    @6
    @13
    @20
    @16
    adantr
    @22
    @2
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @10
    cr
    wcel
    halfpire
    @22
    @19
    cpi
    cmul
    co
    #
    @8
    cr
    @6
    @26
    @8
    wceq
    @20
    @6
    @8
    cpi
    @18
    cpi
    cc
    wcel
    @6
    picn
    a1i
    cpi
    cc0
    wne
    @6
    cpi
    pire
    pipos
    gt0ne0ii
    a1i
    divcan1d
    adantr
    @22
    @19
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @26
    cr
    wcel
    @20
    @27
    @6
    @19
    zre
    adantl
    pire
    @19
    cpi
    remulcl
    sylancl
    eqeltrrd
    @2
    @8
    resubcl
    sylancr
    eqeltrrd
    rered
    @0
    @5
    @20
    simplr
    eqeltrrd
    @23
    cc0
    cz
    wcel
    cc0
    @19
    clt
    wbr
    @19
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    @21
    @23
    0zd
    @23
    @8
    cpi
    @23
    @24
    cA
    cr
    wcel
    #
    @25
    halfpire
    cA
    @3
    @2
    elioore
    #
    @2
    cA
    resubcl
    sylancr
    #
    @28
    @23
    pire
    a1i
    #
    @23
    cA
    @2
    clt
    wbr
    #
    cc0
    @8
    clt
    wbr
    #
    @23
    @3
    cA
    clt
    wbr
    #
    @34
    cA
    @3
    @2
    eliooord
    #
    simprd
    @23
    @30
    @24
    @34
    @35
    wb
    @31
    halfpire
    cA
    @2
    posdif
    sylancl
    mpbid
    cc0
    cpi
    clt
    wbr
    #
    @23
    pipos
    a1i
    #
    divgt0d
    @23
    @19
    c1
    @29
    clt
    @23
    @19
    c1
    clt
    wbr
    #
    @8
    cpi
    c1
    cmul
    co
    #
    clt
    wbr
    #
    @23
    @8
    cpi
    @41
    clt
    @23
    @2
    cpi
    cA
    @24
    @23
    halfpire
    a1i
    @33
    @31
    @23
    @2
    cpi
    cmin
    co
    @3
    cA
    clt
    @2
    cpi
    @3
    @14
    picn
    @2
    @14
    negcli
    cpi
    @3
    caddc
    co
    cpi
    @2
    cmin
    co
    @2
    cpi
    @2
    picn
    @14
    negsubi
    cpi
    @2
    @2
    picn
    @14
    @14
    pidiv2halves
    subaddrii
    eqtri
    subaddrii
    @23
    @36
    @34
    @37
    simpld
    syl5eqbr
    ltsub23d
    cpi
    picn
    mulid1i
    syl6breqr
    @23
    @25
    c1
    cr
    wcel
    @28
    @38
    @40
    @42
    wb
    @32
    @23
    1red
    @33
    @39
    @8
    c1
    cpi
    ltdivmul
    syl112anc
    mpbird
    1e0p1
    syl6breq
    cc0
    @19
    btwnnz
    syl3anc
    syl
    pm2.01da
    @6
    @20
    @9
    cc0
    @6
    @17
    @9
    cc0
    wceq
    @20
    wb
    @18
    @8
    sineq0
    syl
    necon3abid
    mpbird
    eqnetrd
end
