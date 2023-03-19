include "ccos.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "crp.mm"
include "wcel.mm"
include "c2.mm"
include "caddc.mm"
include "cdiv.mm"
include "csin.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "cpi.mm"
include "cicc.mm"
include "w3a.mm"
include "0re.mm"
include "pire.mm"
include "elicc2i.mm"
include "sylib.mm"
include "simp1d.mm"
include "recnd.mm"
include "subcos.mm"
include "syl2anc.mm"
include "2re.mm"
include "2pos.mm"
include "elrpii.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "resincld.mm"
include "cioo.mm"
include "a1i.mm"
include "simp2d.mm"
include "lelttrd.mm"
include "addgtge0.mm"
include "syl22anc.mm"
include "wa.mm"
include "divgt0.mm"
include "mpanr12.mm"
include "ltadd2dd.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "wb.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "simp3d.mm"
include "ltletrd.mm"
include "cxr.mm"
include "0xr.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "sinq12gt0.mm"
include "syl.mm"
include "elrpd.mm"
include "resubcld.mm"
include "posdifd.mm"
include "mpbid.mm"
include "rehalfcl.mm"
include "mp1i.mm"
include "subge02d.mm"
include "letrd.mm"
include "lediv1.mm"
include "pirp.mm"
include "rphalflt.mm"
include "rpmulcld.mm"
include "rpmulcl.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "recoscld.mm"
include "difrp.mm"

theorem cosordlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume cosord.1: |- ( ph -> A e. ( 0 [,] _pi ) )
  assume cosord.2: |- ( ph -> B e. ( 0 [,] _pi ) )
  assume cosord.3: |- ( ph -> A < B )


  assert |- ( ph -> ( cos ` B ) < ( cos ` A ) )

  proof
    wph
    cB
    ccos
    cfv
    #
    cA
    ccos
    cfv
    #
    clt
    wbr
    #
    @1
    @0
    cmin
    co
    #
    crp
    wcel
    #
    wph
    @3
    c2
    cB
    cA
    caddc
    co
    #
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cB
    cA
    cmin
    co
    #
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    crp
    wph
    cB
    cc
    wcel
    cA
    cc
    wcel
    @3
    @12
    wceq
    wph
    cB
    wph
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    cB
    cpi
    cle
    wbr
    #
    wph
    cB
    cc0
    cpi
    cicc
    co
    #
    wcel
    @13
    @14
    @15
    w3a
    cosord.2
    cc0
    cpi
    cB
    0re
    pire
    elicc2i
    sylib
    #
    simp1d
    #
    recnd
    #
    wph
    cA
    wph
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cpi
    cle
    wbr
    #
    wph
    cA
    @16
    wcel
    @20
    @21
    @22
    w3a
    cosord.1
    cc0
    cpi
    cA
    0re
    pire
    elicc2i
    sylib
    #
    simp1d
    #
    recnd
    cB
    cA
    subcos
    syl2anc
    wph
    c2
    crp
    wcel
    @11
    crp
    wcel
    @12
    crp
    wcel
    c2
    2re
    2pos
    elrpii
    wph
    @7
    @10
    wph
    @7
    wph
    @6
    wph
    @5
    wph
    cB
    cA
    @18
    @24
    readdcld
    #
    rehalfcld
    #
    resincld
    wph
    @6
    cc0
    cpi
    cioo
    co
    #
    wcel
    #
    cc0
    @7
    clt
    wbr
    wph
    @6
    cr
    wcel
    #
    cc0
    @6
    clt
    wbr
    #
    @6
    cpi
    clt
    wbr
    #
    @28
    @26
    wph
    @5
    cr
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    @30
    @25
    wph
    @13
    @20
    cc0
    cB
    clt
    wbr
    @21
    @33
    @18
    @24
    wph
    cc0
    cA
    cB
    cc0
    cr
    wcel
    wph
    0re
    a1i
    @24
    @18
    wph
    @20
    @21
    @22
    @23
    simp2d
    #
    cosord.3
    lelttrd
    @34
    cB
    cA
    addgtge0
    syl22anc
    @32
    @33
    wa
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @30
    2re
    2pos
    @5
    c2
    divgt0
    mpanr12
    syl2anc
    wph
    @6
    cB
    cpi
    @26
    @18
    cpi
    cr
    wcel
    #
    wph
    pire
    a1i
    #
    wph
    @6
    cB
    clt
    wbr
    #
    @5
    c2
    cB
    cmul
    co
    #
    clt
    wbr
    #
    wph
    @5
    cB
    cB
    caddc
    co
    @40
    clt
    wph
    cA
    cB
    cB
    @24
    @18
    @18
    cosord.3
    ltadd2dd
    wph
    cB
    @19
    2timesd
    breqtrrd
    wph
    @32
    @13
    @35
    @36
    @39
    @41
    wb
    @25
    @18
    @35
    wph
    2re
    a1i
    #
    @36
    wph
    2pos
    a1i
    #
    @5
    cB
    c2
    ltdivmul
    syl112anc
    mpbird
    wph
    @13
    @14
    @15
    @17
    simp3d
    #
    ltletrd
    cc0
    cxr
    wcel
    #
    cpi
    cxr
    wcel
    #
    @28
    @29
    @30
    @31
    w3a
    wb
    0xr
    cpi
    pire
    rexri
    #
    cc0
    cpi
    @6
    elioo2
    mp2an
    syl3anbrc
    @6
    sinq12gt0
    syl
    elrpd
    wph
    @10
    wph
    @9
    wph
    @8
    wph
    cB
    cA
    @18
    @24
    resubcld
    #
    rehalfcld
    #
    resincld
    wph
    @9
    @27
    wcel
    #
    cc0
    @10
    clt
    wbr
    wph
    @9
    cr
    wcel
    #
    cc0
    @9
    clt
    wbr
    #
    @9
    cpi
    clt
    wbr
    #
    @50
    @49
    wph
    @8
    cr
    wcel
    #
    cc0
    @8
    clt
    wbr
    #
    @52
    @48
    wph
    cA
    cB
    clt
    wbr
    @55
    cosord.3
    wph
    cA
    cB
    @24
    @18
    posdifd
    mpbid
    @54
    @55
    wa
    @35
    @36
    @52
    2re
    2pos
    @8
    c2
    divgt0
    mpanr12
    syl2anc
    wph
    @9
    cpi
    c2
    cdiv
    co
    #
    cpi
    @49
    @37
    @56
    cr
    wcel
    wph
    pire
    cpi
    rehalfcl
    mp1i
    @38
    wph
    @8
    cpi
    cle
    wbr
    #
    @9
    @56
    cle
    wbr
    #
    wph
    @8
    cB
    cpi
    @48
    @18
    @38
    wph
    @21
    @8
    cB
    cle
    wbr
    @34
    wph
    cB
    cA
    @18
    @24
    subge02d
    mpbid
    @44
    letrd
    wph
    @54
    @37
    @35
    @36
    @57
    @58
    wb
    @48
    @38
    @42
    @43
    @8
    cpi
    c2
    lediv1
    syl112anc
    mpbid
    cpi
    crp
    wcel
    @56
    cpi
    clt
    wbr
    wph
    pirp
    cpi
    rphalflt
    mp1i
    lelttrd
    @45
    @46
    @50
    @51
    @52
    @53
    w3a
    wb
    0xr
    @47
    cc0
    cpi
    @9
    elioo2
    mp2an
    syl3anbrc
    @9
    sinq12gt0
    syl
    elrpd
    rpmulcld
    c2
    @11
    rpmulcl
    sylancr
    eqeltrd
    wph
    @0
    cr
    wcel
    @1
    cr
    wcel
    @2
    @4
    wb
    wph
    cB
    @18
    recoscld
    wph
    cA
    @24
    recoscld
    @0
    @1
    difrp
    syl2anc
    mpbird
end
