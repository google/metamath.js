include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "clog.mm"
include "ci.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "ce.mm"
include "wceq.mm"
include "logcl.mm"
include "3adant3.mm"
include "ax-icn.mm"
include "halfpire.mm"
include "recni.mm"
include "mulcli.mm"
include "efadd.mm"
include "sylancl.mm"
include "eflog.mm"
include "efhalfpi.mm"
include "a1i.mm"
include "oveq12d.mm"
include "simp1.mm"
include "mulcom.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "crn.mm"
include "cneg.mm"
include "cim.mm"
include "clt.mm"
include "addcl.mm"
include "cr.mm"
include "pire.mm"
include "renegcli.mm"
include "imcld.mm"
include "readdcl.mm"
include "wa.mm"
include "logimcl.mm"
include "simpld.mm"
include "crp.mm"
include "pirp.mm"
include "rphalfcl.mm"
include "ax-mp.mm"
include "ltaddrp.mm"
include "lttrd.mm"
include "imadd.mm"
include "reim.mm"
include "rere.mm"
include "eqtr3i.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "breqtrrd.mm"
include "cmin.mm"
include "cicc.mm"
include "argrege0.mm"
include "elicc2i.mm"
include "simp3bi.mm"
include "syl.mm"
include "pidiv2halves.mm"
include "subaddrii.mm"
include "syl6breqr.mm"
include "wb.mm"
include "leaddsub.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "ellogrn.mm"
include "syl3anbrc.mm"
include "logef.mm"
include "eqtr3d.mm"

theorem logimul
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 /\ 0 <_ ( Re ` A ) ) -> ( log ` ( _i x. A ) ) = ( ( log ` A ) + ( _i x. ( _pi / 2 ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cc0
    cA
    cre
    cfv
    cle
    wbr
    #
    w3a
    #
    cA
    clog
    cfv
    #
    ci
    cpi
    c2
    cdiv
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    ce
    cfv
    #
    clog
    cfv
    #
    ci
    cA
    cmul
    co
    #
    clog
    cfv
    @7
    @3
    @8
    @10
    clog
    @3
    @8
    @4
    ce
    cfv
    #
    @6
    ce
    cfv
    #
    cmul
    co
    #
    cA
    ci
    cmul
    co
    #
    @10
    @3
    @4
    cc
    wcel
    #
    @6
    cc
    wcel
    #
    @8
    @13
    wceq
    @0
    @1
    @15
    @2
    cA
    logcl
    3adant3
    #
    ci
    @5
    ax-icn
    @5
    halfpire
    recni
    #
    mulcli
    #
    @4
    @6
    efadd
    sylancl
    @3
    @11
    cA
    @12
    ci
    cmul
    @0
    @1
    @11
    cA
    wceq
    @2
    cA
    eflog
    3adant3
    @12
    ci
    wceq
    @3
    efhalfpi
    a1i
    oveq12d
    @3
    @0
    ci
    cc
    wcel
    @14
    @10
    wceq
    @0
    @1
    @2
    simp1
    ax-icn
    cA
    ci
    mulcom
    sylancl
    3eqtrd
    fveq2d
    @3
    @7
    clog
    crn
    wcel
    #
    @9
    @7
    wceq
    @3
    @7
    cc
    wcel
    #
    cpi
    cneg
    #
    @7
    cim
    cfv
    #
    clt
    wbr
    @23
    cpi
    cle
    wbr
    @20
    @3
    @15
    @16
    @21
    @17
    @19
    @4
    @6
    addcl
    sylancl
    @3
    @22
    @4
    cim
    cfv
    #
    @5
    caddc
    co
    #
    @23
    clt
    @3
    @22
    @24
    @25
    @22
    cr
    wcel
    @3
    cpi
    pire
    renegcli
    a1i
    @3
    @4
    @17
    imcld
    #
    @3
    @24
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @25
    cr
    wcel
    @26
    halfpire
    @24
    @5
    readdcl
    sylancl
    @3
    @22
    @24
    clt
    wbr
    #
    @24
    cpi
    cle
    wbr
    #
    @0
    @1
    @29
    @30
    wa
    @2
    cA
    logimcl
    3adant3
    simpld
    @3
    @27
    @5
    crp
    wcel
    #
    @24
    @25
    clt
    wbr
    @26
    cpi
    crp
    wcel
    @31
    pirp
    cpi
    rphalfcl
    ax-mp
    @24
    @5
    ltaddrp
    sylancl
    lttrd
    @3
    @23
    @24
    @6
    cim
    cfv
    #
    caddc
    co
    #
    @25
    @3
    @15
    @16
    @23
    @33
    wceq
    @17
    @19
    @4
    @6
    imadd
    sylancl
    @32
    @5
    @24
    caddc
    @5
    cre
    cfv
    #
    @32
    @5
    @5
    cc
    wcel
    @34
    @32
    wceq
    @18
    @5
    reim
    ax-mp
    @28
    @34
    @5
    wceq
    halfpire
    @5
    rere
    ax-mp
    eqtr3i
    oveq2i
    syl6eq
    #
    breqtrrd
    @3
    @23
    @25
    cpi
    cle
    @35
    @3
    @25
    cpi
    cle
    wbr
    #
    @24
    cpi
    @5
    cmin
    co
    #
    cle
    wbr
    #
    @3
    @24
    @5
    @37
    cle
    @3
    @24
    @5
    cneg
    #
    @5
    cicc
    co
    wcel
    #
    @24
    @5
    cle
    wbr
    #
    cA
    argrege0
    @40
    @27
    @39
    @24
    cle
    wbr
    @41
    @39
    @5
    @24
    @5
    halfpire
    renegcli
    halfpire
    elicc2i
    simp3bi
    syl
    cpi
    @5
    @5
    cpi
    pire
    recni
    @18
    @18
    pidiv2halves
    subaddrii
    syl6breqr
    @3
    @27
    @28
    cpi
    cr
    wcel
    #
    @36
    @38
    wb
    @26
    @28
    @3
    halfpire
    a1i
    @42
    @3
    pire
    a1i
    @24
    @5
    cpi
    leaddsub
    syl3anc
    mpbird
    eqbrtrd
    @7
    ellogrn
    syl3anbrc
    @7
    logef
    syl
    eqtr3d
end
