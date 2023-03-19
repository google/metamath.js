include "c3.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "clt.mm"
include "1re.mm"
include "3re.mm"
include "rehalfcli.mm"
include "cmul.mm"
include "2cn.mm"
include "mulid2i.mm"
include "2lt3.mm"
include "eqbrtri.mm"
include "cc0.mm"
include "wb.mm"
include "2pos.mm"
include "2re.mm"
include "ltmuldivi.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "ltleii.mm"
include "c4.mm"
include "3lt4.mm"
include "2t2e4.mm"
include "breqtrri.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "pm3.2i.mm"
include "ltdivmul.mm"
include "mp3an.mm"
include "mpbir.mm"
include "df-2.mm"
include "breqtri.mm"
include "cz.mm"
include "1z.mm"
include "flbi.mm"
include "mp2an.mm"
include "mpbir2an.mm"
include "renegcli.mm"
include "ltnegi.mm"
include "cmin.mm"
include "cc.mm"
include "negcli.mm"
include "ax-1cn.mm"
include "negdi2.mm"
include "negnegi.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "2m1e1.mm"
include "readdcli.mm"
include "ltnegcon1i.mm"
include "2z.mm"
include "znegcl.mm"

theorem ex-fl



  assert |- ( ( |_ ` ( 3 / 2 ) ) = 1 /\ ( |_ ` -u ( 3 / 2 ) ) = -u 2 )

  proof
    c3
    c2
    cdiv
    co
    #
    cfl
    cfv
    c1
    wceq
    #
    @0
    cneg
    #
    cfl
    cfv
    c2
    cneg
    #
    wceq
    #
    @1
    c1
    @0
    cle
    wbr
    #
    @0
    c1
    c1
    caddc
    co
    #
    clt
    wbr
    #
    c1
    @0
    1re
    c3
    3re
    rehalfcli
    #
    c1
    c2
    cmul
    co
    #
    c3
    clt
    wbr
    #
    c1
    @0
    clt
    wbr
    #
    @9
    c2
    c3
    clt
    c2
    2cn
    mulid2i
    2lt3
    eqbrtri
    cc0
    c2
    clt
    wbr
    #
    @10
    @11
    wb
    2pos
    c1
    c3
    c2
    1re
    3re
    2re
    ltmuldivi
    ax-mp
    mpbi
    #
    ltleii
    @0
    c2
    @6
    clt
    @0
    c2
    clt
    wbr
    #
    c3
    c2
    c2
    cmul
    co
    #
    clt
    wbr
    #
    c3
    c4
    @15
    clt
    3lt4
    2t2e4
    breqtrri
    c3
    cr
    wcel
    c2
    cr
    wcel
    #
    @17
    @12
    wa
    @14
    @16
    wb
    3re
    2re
    @17
    @12
    2re
    2pos
    pm3.2i
    c3
    c2
    c2
    ltdivmul
    mp3an
    mpbir
    #
    df-2
    breqtri
    @0
    cr
    wcel
    c1
    cz
    wcel
    @1
    @5
    @7
    wa
    wb
    @8
    1z
    @0
    c1
    flbi
    mp2an
    mpbir2an
    @4
    @3
    @2
    cle
    wbr
    #
    @2
    @3
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @3
    @2
    c2
    2re
    renegcli
    #
    @0
    @8
    renegcli
    #
    @14
    @3
    @2
    clt
    wbr
    @18
    @0
    c2
    @8
    2re
    ltnegi
    mpbi
    ltleii
    @20
    cneg
    #
    @0
    clt
    wbr
    @21
    @24
    c2
    c1
    cmin
    co
    #
    @0
    clt
    @24
    @3
    cneg
    #
    c1
    cmin
    co
    #
    @25
    @3
    cc
    wcel
    c1
    cc
    wcel
    @24
    @27
    wceq
    c2
    2cn
    negcli
    ax-1cn
    @3
    c1
    negdi2
    mp2an
    @26
    c2
    c1
    cmin
    c2
    2cn
    negnegi
    oveq1i
    eqtri
    @25
    c1
    @0
    clt
    2m1e1
    @13
    eqbrtri
    eqbrtri
    @20
    @0
    @3
    c1
    @22
    1re
    readdcli
    @8
    ltnegcon1i
    mpbi
    @2
    cr
    wcel
    @3
    cz
    wcel
    #
    @4
    @19
    @21
    wa
    wb
    @23
    c2
    cz
    wcel
    @28
    2z
    c2
    znegcl
    ax-mp
    @2
    @3
    flbi
    mp2an
    mpbir2an
    pm3.2i
end
