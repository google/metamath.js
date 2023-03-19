include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cim.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "clog.mm"
include "ci.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "ce.mm"
include "cneg.mm"
include "cdiv.mm"
include "c1.mm"
include "wceq.mm"
include "wne.mm"
include "cr.mm"
include "imcl.mm"
include "gt0ne0.mm"
include "sylan.mm"
include "fveq2.mm"
include "im0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "syl.mm"
include "logcl.mm"
include "syldan.mm"
include "ax-icn.mm"
include "picn.mm"
include "mulcli.mm"
include "efsub.mm"
include "sylancl.mm"
include "eflog.mm"
include "efipi.mm"
include "a1i.mm"
include "oveq12d.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "divneg2.mm"
include "mp3an23.mm"
include "div1.mm"
include "negeqd.mm"
include "eqtr3d.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "crn.mm"
include "cle.mm"
include "subcl.mm"
include "caddc.mm"
include "cioo.mm"
include "argimgt0.mm"
include "eliooord.mm"
include "simpld.mm"
include "wb.mm"
include "pire.mm"
include "renegcli.mm"
include "ltaddpos2.mm"
include "mpbid.mm"
include "recnd.mm"
include "negsub.mm"
include "breqtrd.mm"
include "imsub.mm"
include "cre.mm"
include "reim.mm"
include "ax-mp.mm"
include "rere.mm"
include "eqtr3i.mm"
include "oveq2i.mm"
include "breqtrrd.mm"
include "resubcl.mm"
include "0re.mm"
include "pipos.mm"
include "ltleii.mm"
include "subge02.mm"
include "mpbii.mm"
include "logimcl.mm"
include "simprd.mm"
include "letrd.mm"
include "eqbrtrd.mm"
include "ellogrn.mm"
include "syl3anbrc.mm"
include "logef.mm"

theorem logneg2
  let cA: class A


  assert |- ( ( A e. CC /\ 0 < ( Im ` A ) ) -> ( log ` -u A ) = ( ( log ` A ) - ( _i x. _pi ) ) )

  proof
    cA
    cc
    wcel
    #
    cc0
    cA
    cim
    cfv
    #
    clt
    wbr
    #
    wa
    #
    cA
    clog
    cfv
    #
    ci
    cpi
    cmul
    co
    #
    cmin
    co
    #
    ce
    cfv
    #
    clog
    cfv
    #
    cA
    cneg
    #
    clog
    cfv
    @6
    @3
    @7
    @9
    clog
    @3
    @7
    @4
    ce
    cfv
    #
    @5
    ce
    cfv
    #
    cdiv
    co
    #
    cA
    c1
    cneg
    #
    cdiv
    co
    #
    @9
    @3
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @7
    @12
    wceq
    @0
    @2
    cA
    cc0
    wne
    #
    @15
    @3
    @1
    cc0
    wne
    #
    @17
    @0
    @1
    cr
    wcel
    @2
    @18
    cA
    imcl
    @1
    gt0ne0
    sylan
    cA
    cc0
    @1
    cc0
    cA
    cc0
    wceq
    @1
    cc0
    cim
    cfv
    cc0
    cA
    cc0
    cim
    fveq2
    im0
    syl6eq
    necon3i
    syl
    #
    cA
    logcl
    syldan
    #
    ci
    cpi
    ax-icn
    picn
    mulcli
    #
    @4
    @5
    efsub
    sylancl
    @3
    @10
    cA
    @11
    @13
    cdiv
    @0
    @2
    @17
    @10
    cA
    wceq
    @19
    cA
    eflog
    syldan
    @11
    @13
    wceq
    @3
    efipi
    a1i
    oveq12d
    @0
    @14
    @9
    wceq
    @2
    @0
    cA
    c1
    cdiv
    co
    #
    cneg
    #
    @14
    @9
    @0
    c1
    cc
    wcel
    c1
    cc0
    wne
    @23
    @14
    wceq
    ax-1cn
    ax-1ne0
    cA
    c1
    divneg2
    mp3an23
    @0
    @22
    cA
    cA
    div1
    negeqd
    eqtr3d
    adantr
    3eqtrd
    fveq2d
    @3
    @6
    clog
    crn
    wcel
    #
    @8
    @6
    wceq
    @3
    @6
    cc
    wcel
    #
    cpi
    cneg
    #
    @6
    cim
    cfv
    #
    clt
    wbr
    @27
    cpi
    cle
    wbr
    @24
    @3
    @15
    @16
    @25
    @20
    @21
    @4
    @5
    subcl
    sylancl
    @3
    @26
    @4
    cim
    cfv
    #
    cpi
    cmin
    co
    #
    @27
    clt
    @3
    @26
    @28
    @26
    caddc
    co
    #
    @29
    clt
    @3
    cc0
    @28
    clt
    wbr
    #
    @26
    @30
    clt
    wbr
    #
    @3
    @31
    @28
    cpi
    clt
    wbr
    #
    @3
    @28
    cc0
    cpi
    cioo
    co
    wcel
    @31
    @33
    wa
    cA
    argimgt0
    @28
    cc0
    cpi
    eliooord
    syl
    simpld
    @3
    @28
    cr
    wcel
    #
    @26
    cr
    wcel
    @31
    @32
    wb
    @3
    @15
    @34
    @20
    @4
    imcl
    syl
    #
    cpi
    pire
    renegcli
    @28
    @26
    ltaddpos2
    sylancl
    mpbid
    @3
    @28
    cc
    wcel
    cpi
    cc
    wcel
    #
    @30
    @29
    wceq
    @3
    @28
    @35
    recnd
    picn
    @28
    cpi
    negsub
    sylancl
    breqtrd
    @3
    @27
    @28
    @5
    cim
    cfv
    #
    cmin
    co
    #
    @29
    @3
    @15
    @16
    @27
    @38
    wceq
    @20
    @21
    @4
    @5
    imsub
    sylancl
    @37
    cpi
    @28
    cmin
    cpi
    cre
    cfv
    #
    @37
    cpi
    @36
    @39
    @37
    wceq
    picn
    cpi
    reim
    ax-mp
    cpi
    cr
    wcel
    #
    @39
    cpi
    wceq
    pire
    cpi
    rere
    ax-mp
    eqtr3i
    oveq2i
    syl6eq
    #
    breqtrrd
    @3
    @27
    @29
    cpi
    cle
    @41
    @3
    @29
    @28
    cpi
    @3
    @34
    @40
    @29
    cr
    wcel
    @35
    pire
    @28
    cpi
    resubcl
    sylancl
    @35
    @40
    @3
    pire
    a1i
    @3
    cc0
    cpi
    cle
    wbr
    #
    @29
    @28
    cle
    wbr
    #
    cc0
    cpi
    0re
    pire
    pipos
    ltleii
    @3
    @34
    @40
    @42
    @43
    wb
    @35
    pire
    @28
    cpi
    subge02
    sylancl
    mpbii
    @3
    @26
    @28
    clt
    wbr
    #
    @28
    cpi
    cle
    wbr
    #
    @0
    @2
    @17
    @44
    @45
    wa
    @19
    cA
    logimcl
    syldan
    simprd
    letrd
    eqbrtrd
    @6
    ellogrn
    syl3anbrc
    @6
    logef
    syl
    eqtr3d
end
