include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "cle.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "cn.mm"
include "wb.mm"
include "prmnn.mm"
include "nnnn0.mm"
include "oddnn02np1.mm"
include "3syl.mm"
include "wa.mm"
include "cif.mm"
include "iftrue.mm"
include "adantr.mm"
include "2nn.mm"
include "nn0ledivnn.mm"
include "mpan2.mm"
include "adantl.mm"
include "eqbrtrd.mm"
include "iffalse.mm"
include "cr.mm"
include "nn0re.mm"
include "peano2rem.mm"
include "rehalfcld.mm"
include "syl.mm"
include "lem1d.mm"
include "cc0.mm"
include "clt.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "lediv1.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "letrd.mm"
include "pm2.61ian.mm"
include "ad2antlr.mm"
include "cz.mm"
include "nn0z.mm"
include "eqcom.mm"
include "biimpi.mm"
include "flodddiv4.mm"
include "syl2an.mm"
include "oveq1.mm"
include "eqcoms.mm"
include "cc.mm"
include "2nn0.mm"
include "id.mm"
include "nn0mulcld.mm"
include "nn0cnd.mm"
include "pncan1.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "nn0cn.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "3brtr4d.mm"
include "ex.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "imp.mm"

theorem 2lgslem1c
  let cP: class P
  let vn: setvar n


  assert |- ( ( P e. Prime /\ -. 2 || P ) -> ( |_ ` ( P / 4 ) ) <_ ( ( P - 1 ) / 2 ) )

  proof
    cP
    cprime
    wcel
    #
    c2
    cP
    cdvds
    wbr
    wn
    #
    cP
    c4
    cdiv
    co
    cfl
    cfv
    #
    cP
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    @0
    @1
    c2
    vn
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cP
    wceq
    #
    vn
    cn0
    wrex
    #
    @5
    @0
    cP
    cn
    wcel
    cP
    cn0
    wcel
    @1
    @10
    wb
    cP
    prmnn
    cP
    nnnn0
    vn
    cP
    oddnn02np1
    3syl
    @0
    @9
    @5
    vn
    cn0
    @0
    @6
    cn0
    wcel
    #
    wa
    #
    @9
    @5
    @12
    @9
    wa
    #
    c2
    @6
    cdvds
    wbr
    #
    @6
    c2
    cdiv
    co
    #
    @6
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cif
    #
    @6
    @2
    @4
    cle
    @11
    @18
    @6
    cle
    wbr
    #
    @0
    @9
    @14
    @11
    @19
    @14
    @11
    wa
    @18
    @15
    @6
    cle
    @14
    @18
    @15
    wceq
    @11
    @14
    @15
    @17
    iftrue
    adantr
    @11
    @15
    @6
    cle
    wbr
    #
    @14
    @11
    c2
    cn
    wcel
    @20
    2nn
    @6
    c2
    nn0ledivnn
    mpan2
    #
    adantl
    eqbrtrd
    @14
    wn
    #
    @11
    wa
    @18
    @17
    @6
    cle
    @22
    @18
    @17
    wceq
    @11
    @14
    @15
    @17
    iffalse
    adantr
    @11
    @17
    @6
    cle
    wbr
    @22
    @11
    @17
    @15
    @6
    @11
    @6
    cr
    wcel
    #
    @17
    cr
    wcel
    @6
    nn0re
    #
    @23
    @16
    @6
    peano2rem
    #
    rehalfcld
    syl
    @11
    @6
    @24
    rehalfcld
    @24
    @11
    @16
    @6
    cle
    wbr
    #
    @17
    @15
    cle
    wbr
    #
    @11
    @6
    @24
    lem1d
    @11
    @16
    cr
    wcel
    #
    @23
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @26
    @27
    wb
    @11
    @23
    @28
    @24
    @25
    syl
    @24
    @31
    @11
    @29
    @30
    2re
    2pos
    pm3.2i
    a1i
    @16
    @6
    c2
    lediv1
    syl3anc
    mpbid
    @21
    letrd
    adantl
    eqbrtrd
    pm2.61ian
    ad2antlr
    @12
    @6
    cz
    wcel
    #
    cP
    @8
    wceq
    #
    @2
    @18
    wceq
    @9
    @11
    @32
    @0
    @6
    nn0z
    adantl
    @9
    @33
    @8
    cP
    eqcom
    biimpi
    @6
    cP
    flodddiv4
    syl2an
    @13
    @4
    @7
    c2
    cdiv
    co
    #
    @6
    @13
    @3
    @7
    c2
    cdiv
    @13
    @3
    @8
    c1
    cmin
    co
    #
    @7
    @9
    @3
    @35
    wceq
    #
    @12
    @36
    cP
    @8
    cP
    @8
    c1
    cmin
    oveq1
    eqcoms
    adantl
    @11
    @35
    @7
    wceq
    #
    @0
    @9
    @11
    @7
    cc
    wcel
    @37
    @11
    @7
    @11
    c2
    @6
    c2
    cn0
    wcel
    @11
    2nn0
    a1i
    @11
    id
    nn0mulcld
    nn0cnd
    @7
    pncan1
    syl
    ad2antlr
    eqtrd
    oveq1d
    @11
    @34
    @6
    wceq
    @0
    @9
    @11
    @6
    c2
    @6
    nn0cn
    @11
    2cnd
    c2
    cc0
    wne
    @11
    2ne0
    a1i
    divcan3d
    ad2antlr
    eqtrd
    3brtr4d
    ex
    rexlimdva
    sylbid
    imp
end
