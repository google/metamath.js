include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "cmo.mm"
include "wceq.mm"
include "cdiv.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "0zd.mm"
include "cr.mm"
include "wss.mm"
include "pire.mm"
include "renegcli.mm"
include "iccssre.mm"
include "mp2an.mm"
include "eldifi.mm"
include "sseldi.mm"
include "adantr.mm"
include "2re.mm"
include "remulcli.mm"
include "a1i.mm"
include "simpr.mm"
include "2pos.mm"
include "pipos.mm"
include "mulgt0ii.mm"
include "divgt0d.mm"
include "elrpd.mm"
include "cxr.mm"
include "cle.mm"
include "rexri.mm"
include "rexrd.mm"
include "iccleub.mm"
include "syl3anc.mm"
include "crp.mm"
include "pirp.mm"
include "2timesgt.mm"
include "mp1i.mm"
include "lelttrd.mm"
include "ltdiv1dd.mm"
include "recni.mm"
include "gt0ne0ii.mm"
include "dividi.mm"
include "syl6breq.mm"
include "0p1e1.mm"
include "syl6breqr.mm"
include "btwnnz.mm"
include "simpl.mm"
include "0red.mm"
include "nltled.mm"
include "wne.mm"
include "eldifsni.mm"
include "necomd.mm"
include "leneltd.mm"
include "neg1z.mm"
include "redivcld.mm"
include "1red.mm"
include "cc.mm"
include "recnd.mm"
include "divnegd.mm"
include "renegcld.mm"
include "2rp.mm"
include "rpmulcl.mm"
include "iccgelb.mm"
include "lenegcon1d.mm"
include "eqbrtrd.mm"
include "ltnegcon1d.mm"
include "divlt0gt0d.mm"
include "neg1cn.mm"
include "ax-1cn.mm"
include "addcomi.mm"
include "1pneg1e0.mm"
include "eqtr2i.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "wb.mm"
include "mod0.mm"
include "mtbird.mm"
include "neqned.mm"

theorem fourierdlem24
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. ( ( -u _pi [,] _pi ) \ { 0 } ) -> ( A mod ( 2 x. _pi ) ) =/= 0 )

  proof
    cA
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    cc0
    csn
    #
    cdif
    wcel
    #
    cA
    c2
    cpi
    cmul
    co
    #
    cmo
    co
    #
    cc0
    @3
    @5
    cc0
    wceq
    #
    cA
    @4
    cdiv
    co
    #
    cz
    wcel
    #
    @3
    cc0
    cA
    clt
    wbr
    #
    @8
    wn
    #
    @3
    @9
    wa
    #
    cc0
    cz
    wcel
    cc0
    @7
    clt
    wbr
    @7
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    @10
    @11
    0zd
    @11
    cA
    @4
    @3
    cA
    cr
    wcel
    #
    @9
    @3
    @1
    cr
    cA
    @0
    cr
    wcel
    cpi
    cr
    wcel
    #
    @1
    cr
    wss
    cpi
    pire
    renegcli
    #
    pire
    @0
    cpi
    iccssre
    mp2an
    cA
    @1
    @2
    eldifi
    #
    sseldi
    #
    adantr
    #
    @4
    cr
    wcel
    #
    @11
    c2
    cpi
    2re
    pire
    remulcli
    #
    a1i
    #
    @3
    @9
    simpr
    cc0
    @4
    clt
    wbr
    @11
    c2
    cpi
    2re
    pire
    2pos
    pipos
    mulgt0ii
    #
    a1i
    #
    divgt0d
    @11
    @7
    c1
    @12
    clt
    @11
    @7
    @4
    @4
    cdiv
    co
    #
    c1
    clt
    @11
    cA
    @4
    @4
    @18
    @21
    @11
    @4
    @21
    @23
    elrpd
    @3
    cA
    @4
    clt
    wbr
    @9
    @3
    cA
    cpi
    @4
    @17
    @14
    @3
    pire
    a1i
    #
    @19
    @3
    @20
    a1i
    #
    @3
    @0
    cxr
    wcel
    #
    cpi
    cxr
    wcel
    #
    cA
    @1
    wcel
    #
    cA
    cpi
    cle
    wbr
    @27
    @3
    @0
    @15
    rexri
    a1i
    #
    @3
    cpi
    @25
    rexrd
    #
    @16
    @0
    cpi
    cA
    iccleub
    syl3anc
    cpi
    crp
    wcel
    #
    cpi
    @4
    clt
    wbr
    @3
    pirp
    cpi
    2timesgt
    mp1i
    #
    lelttrd
    adantr
    ltdiv1dd
    @4
    @4
    @20
    recni
    #
    @4
    @20
    @22
    gt0ne0ii
    #
    dividi
    #
    syl6breq
    0p1e1
    syl6breqr
    cc0
    @7
    btwnnz
    syl3anc
    @3
    @9
    wn
    #
    wa
    #
    @3
    cA
    cc0
    clt
    wbr
    #
    @10
    @3
    @37
    simpl
    @38
    cA
    cc0
    @3
    @13
    @37
    @17
    adantr
    #
    @38
    0red
    #
    @38
    cA
    cc0
    @40
    @41
    @3
    @37
    simpr
    nltled
    @3
    cc0
    cA
    wne
    @37
    @3
    cA
    cc0
    cA
    @1
    cc0
    eldifsni
    necomd
    adantr
    leneltd
    @3
    @39
    wa
    #
    c1
    cneg
    #
    cz
    wcel
    #
    @43
    @7
    clt
    wbr
    @7
    @43
    c1
    caddc
    co
    #
    clt
    wbr
    @10
    @44
    @42
    neg1z
    a1i
    @42
    @7
    c1
    @3
    @7
    cr
    wcel
    @39
    @3
    cA
    @4
    @17
    @26
    @4
    cc0
    wne
    #
    @3
    @35
    a1i
    redivcld
    adantr
    @42
    1red
    @42
    @7
    cneg
    cA
    cneg
    #
    @4
    cdiv
    co
    #
    c1
    clt
    @42
    cA
    @4
    @3
    cA
    cc
    wcel
    @39
    @3
    cA
    @17
    recnd
    adantr
    @4
    cc
    wcel
    @42
    @34
    a1i
    @46
    @42
    @35
    a1i
    divnegd
    @42
    @48
    @24
    c1
    clt
    @42
    @47
    @4
    @4
    @3
    @47
    cr
    wcel
    @39
    @3
    cA
    @17
    renegcld
    #
    adantr
    @19
    @42
    @20
    a1i
    @4
    crp
    wcel
    #
    @42
    c2
    crp
    wcel
    @32
    @50
    2rp
    pirp
    c2
    cpi
    rpmulcl
    mp2an
    #
    a1i
    #
    @3
    @47
    @4
    clt
    wbr
    @39
    @3
    @47
    cpi
    @4
    @49
    @25
    @26
    @3
    cpi
    cA
    @25
    @17
    @3
    @27
    @28
    @29
    @0
    cA
    cle
    wbr
    @30
    @31
    @16
    @0
    cpi
    cA
    iccgelb
    syl3anc
    lenegcon1d
    @33
    lelttrd
    adantr
    ltdiv1dd
    @36
    syl6breq
    eqbrtrd
    ltnegcon1d
    @42
    @7
    cc0
    @45
    clt
    @42
    cA
    @4
    @3
    @13
    @39
    @17
    adantr
    @52
    @3
    @39
    simpr
    divlt0gt0d
    @45
    c1
    @43
    caddc
    co
    cc0
    @43
    c1
    neg1cn
    ax-1cn
    addcomi
    1pneg1e0
    eqtr2i
    syl6breq
    @43
    @7
    btwnnz
    syl3anc
    syl2anc
    pm2.61dan
    @3
    @13
    @50
    @6
    @8
    wb
    @17
    @50
    @3
    @51
    a1i
    cA
    @4
    mod0
    syl2anc
    mtbird
    neqned
end
