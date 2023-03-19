include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "clgs.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cv.mm"
include "cexp.mm"
include "cmo.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wrex.mm"
include "lgsqrmod.mm"
include "imp.mm"
include "cmin.mm"
include "cn.mm"
include "wb.mm"
include "eldifi.mm"
include "prmnn.mm"
include "syl.mm"
include "ad3antlr.mm"
include "zsqcl.mm"
include "adantl.mm"
include "simplll.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "wi.mm"
include "w3a.mm"
include "nnzd.mm"
include "3jca.mm"
include "dvdssub2.mm"
include "sylan.mm"
include "ex.mm"
include "bicom.mm"
include "simpr.mm"
include "2nn.mm"
include "a1i.mm"
include "prmdvdsexp.mm"
include "biimparc.mm"
include "bianir.mm"
include "cc0.mm"
include "ad2antlr.mm"
include "dvdsmod0.mm"
include "lgsprme0.mm"
include "sylan2.mm"
include "eqeq1.mm"
include "wne.mm"
include "0ne1.mm"
include "eqneqall.mm"
include "mpi.mm"
include "syl6bi.mm"
include "syl6bir.mm"
include "com23.mm"
include "syld.mm"
include "ad2antrl.mm"
include "syl5com.mm"
include "mpcom.mm"
include "syl5bi.mm"
include "2a1.mm"
include "pm2.61i.mm"
include "sylbid.mm"
include "ancld.mm"
include "reximdva.mm"
include "mpd.mm"

theorem lgsqrmodndvds
  let vx: setvar x
  let cA: class A
  let cP: class P

  disjoint A x
  disjoint P x
  assert |- ( ( A e. ZZ /\ P e. ( Prime \ { 2 } ) ) -> ( ( A /L P ) = 1 -> E. x e. ZZ ( ( ( x ^ 2 ) mod P ) = ( A mod P ) /\ -. P || x ) ) )

  proof
    cA
    cz
    wcel
    #
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    wa
    #
    cA
    cP
    clgs
    co
    #
    c1
    wceq
    #
    vx
    cv
    #
    c2
    cexp
    co
    #
    cP
    cmo
    co
    cA
    cP
    cmo
    co
    #
    wceq
    #
    cP
    @6
    cdvds
    wbr
    #
    wn
    #
    wa
    #
    vx
    cz
    wrex
    #
    @3
    @5
    wa
    #
    @9
    vx
    cz
    wrex
    #
    @13
    @3
    @5
    @15
    vx
    cA
    cP
    lgsqrmod
    imp
    @14
    @9
    @12
    vx
    cz
    @14
    @6
    cz
    wcel
    #
    wa
    #
    @9
    @11
    @17
    @9
    cP
    @7
    cA
    cmin
    co
    cdvds
    wbr
    #
    @11
    @17
    cP
    cn
    wcel
    #
    @7
    cz
    wcel
    #
    @0
    @9
    @18
    wb
    @2
    @19
    @0
    @5
    @16
    @2
    cP
    cprime
    wcel
    #
    @19
    cP
    cprime
    @1
    eldifi
    #
    cP
    prmnn
    syl
    #
    ad3antlr
    @16
    @20
    @14
    @6
    zsqcl
    adantl
    #
    @0
    @2
    @5
    @16
    simplll
    #
    @7
    cA
    cP
    moddvds
    syl3anc
    @10
    @17
    @18
    @11
    wi
    #
    wi
    @10
    @17
    @26
    @10
    @17
    wa
    #
    @18
    cP
    @7
    cdvds
    wbr
    #
    cP
    cA
    cdvds
    wbr
    #
    wb
    #
    @11
    @27
    @18
    @30
    @27
    cP
    cz
    wcel
    #
    @20
    @0
    w3a
    #
    @18
    @30
    @17
    @32
    @10
    @17
    @31
    @20
    @0
    @2
    @31
    @0
    @5
    @16
    @2
    cP
    @23
    nnzd
    ad3antlr
    @24
    @25
    3jca
    adantl
    cP
    @7
    cA
    dvdssub2
    sylan
    ex
    @30
    @29
    @28
    wb
    #
    @27
    @11
    @28
    @29
    bicom
    @28
    @27
    @33
    @11
    wi
    @17
    @28
    @10
    @17
    @21
    @16
    c2
    cn
    wcel
    #
    @28
    @10
    wb
    @2
    @21
    @0
    @5
    @16
    @22
    ad3antlr
    @14
    @16
    simpr
    @34
    @17
    2nn
    a1i
    @6
    cP
    c2
    prmdvdsexp
    syl3anc
    biimparc
    @28
    @33
    @27
    @11
    @28
    @33
    @27
    @11
    wi
    @28
    @33
    wa
    @29
    @27
    @11
    @28
    @29
    bianir
    @14
    @29
    @11
    wi
    @10
    @16
    @14
    @29
    @8
    cc0
    wceq
    #
    @11
    @14
    @19
    @29
    @35
    wi
    @2
    @19
    @0
    @5
    @23
    ad2antlr
    @19
    @29
    @35
    cP
    cA
    dvdsmod0
    ex
    syl
    @3
    @5
    @35
    @11
    wi
    @3
    @35
    @5
    @11
    @3
    @35
    @4
    cc0
    wceq
    #
    @5
    @11
    wi
    @2
    @0
    @21
    @36
    @35
    wb
    @22
    cA
    cP
    lgsprme0
    sylan2
    @36
    @5
    cc0
    c1
    wceq
    #
    @11
    @4
    cc0
    c1
    eqeq1
    @37
    cc0
    c1
    wne
    @11
    0ne1
    @11
    cc0
    c1
    eqneqall
    mpi
    syl6bi
    syl6bir
    com23
    imp
    syld
    ad2antrl
    syl5com
    ex
    com23
    mpcom
    syl5bi
    syld
    ex
    @11
    @17
    @18
    2a1
    pm2.61i
    sylbid
    ancld
    reximdva
    mpd
    ex
end
