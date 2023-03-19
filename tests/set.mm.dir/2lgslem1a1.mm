include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "cdiv.mm"
include "cfz.mm"
include "cr.mm"
include "crp.mm"
include "cc0.mm"
include "cle.mm"
include "clt.mm"
include "nnrp.mm"
include "adantr.mm"
include "cz.mm"
include "elfzelz.mm"
include "zre.mm"
include "2re.mm"
include "a1i.mm"
include "remulcld.mm"
include "syl.mm"
include "anim12ci.mm"
include "elfznn.mm"
include "nnre.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "0le2.mm"
include "pm3.2i.mm"
include "mulge0.mm"
include "syl21anc.mm"
include "adantl.mm"
include "w3a.mm"
include "wi.mm"
include "elfz2.mm"
include "wb.mm"
include "3ad2ant3.mm"
include "3ad2ant2.mm"
include "2pos.mm"
include "lemul1.mm"
include "syl3anc.mm"
include "cc.mm"
include "nncn.mm"
include "peano2cnm.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan1d.mm"
include "breq2d.mm"
include "id.mm"
include "2z.mm"
include "zmulcld.mm"
include "nnz.mm"
include "zltlem1.mm"
include "syl2an.mm"
include "biimprd.mm"
include "sylbid.mm"
include "ex.mm"
include "com23.mm"
include "a1d.mm"
include "imp32.mm"
include "sylbi.mm"
include "impcom.mm"
include "modid.mm"
include "syl12anc.mm"
include "eqcomd.mm"
include "ralrimiva.mm"

theorem 2lgslem1a1
  let cP: class P
  let vi: setvar i

  disjoint P i
  assert |- ( ( P e. NN /\ -. 2 || P ) -> A. i e. ( 1 ... ( ( P - 1 ) / 2 ) ) ( i x. 2 ) = ( ( i x. 2 ) mod P ) )

  proof
    cP
    cn
    wcel
    #
    c2
    cP
    cdvds
    wbr
    wn
    #
    wa
    #
    vi
    cv
    #
    c2
    cmul
    co
    #
    @4
    cP
    cmo
    co
    #
    wceq
    vi
    c1
    cP
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cfz
    co
    #
    @2
    @3
    @8
    wcel
    #
    wa
    #
    @5
    @4
    @10
    @4
    cr
    wcel
    #
    cP
    crp
    wcel
    #
    wa
    cc0
    @4
    cle
    wbr
    #
    @4
    cP
    clt
    wbr
    #
    @5
    @4
    wceq
    @2
    @12
    @9
    @11
    @0
    @12
    @1
    cP
    nnrp
    adantr
    @9
    @3
    cz
    wcel
    #
    @11
    @3
    c1
    @7
    elfzelz
    @15
    @3
    c2
    @3
    zre
    #
    c2
    cr
    wcel
    #
    @15
    2re
    a1i
    remulcld
    syl
    anim12ci
    @9
    @13
    @2
    @9
    @3
    cn
    wcel
    #
    @13
    @3
    @7
    elfznn
    @18
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    @17
    cc0
    c2
    cle
    wbr
    #
    wa
    #
    @13
    @3
    nnre
    @18
    @3
    @3
    nnnn0
    nn0ge0d
    @21
    @18
    @17
    @20
    2re
    0le2
    pm3.2i
    a1i
    @3
    c2
    mulge0
    syl21anc
    syl
    adantl
    @9
    @2
    @14
    @9
    c1
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @15
    w3a
    #
    c1
    @3
    cle
    wbr
    #
    @3
    @7
    cle
    wbr
    #
    wa
    wa
    @2
    @14
    wi
    #
    @3
    c1
    @7
    elfz2
    @24
    @25
    @26
    @27
    @24
    @26
    @27
    wi
    @25
    @24
    @26
    @4
    @7
    c2
    cmul
    co
    #
    cle
    wbr
    #
    @27
    @24
    @19
    @7
    cr
    wcel
    #
    @17
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @26
    @29
    wb
    @15
    @22
    @19
    @23
    @16
    3ad2ant3
    @23
    @22
    @30
    @15
    @7
    zre
    3ad2ant2
    @32
    @24
    @17
    @31
    2re
    2pos
    pm3.2i
    a1i
    @3
    @7
    c2
    lemul1
    syl3anc
    @24
    @2
    @29
    @14
    @24
    @2
    @29
    @14
    wi
    @24
    @2
    wa
    #
    @29
    @4
    @6
    cle
    wbr
    #
    @14
    @33
    @28
    @6
    @4
    cle
    @2
    @28
    @6
    wceq
    #
    @24
    @0
    @35
    @1
    @0
    @6
    c2
    @0
    cP
    cc
    wcel
    @6
    cc
    wcel
    cP
    nncn
    cP
    peano2cnm
    syl
    @0
    2cnd
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    divcan1d
    adantr
    adantl
    breq2d
    @33
    @14
    @34
    @24
    @4
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    @14
    @34
    wb
    @2
    @15
    @22
    @36
    @23
    @15
    @3
    c2
    @15
    id
    c2
    cz
    wcel
    @15
    2z
    a1i
    zmulcld
    3ad2ant3
    @0
    @37
    @1
    cP
    nnz
    adantr
    @4
    cP
    zltlem1
    syl2an
    biimprd
    sylbid
    ex
    com23
    sylbid
    a1d
    imp32
    sylbi
    impcom
    @4
    cP
    modid
    syl12anc
    eqcomd
    ralrimiva
end
