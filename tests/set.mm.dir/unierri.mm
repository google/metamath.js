include "ccom.mm"
include "chod.mm"
include "co.mm"
include "cnop.mm"
include "cfv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "chil.mm"
include "c0h.mm"
include "wceq.mm"
include "cc0.mm"
include "wf.mm"
include "cbo.mm"
include "wcel.mm"
include "cuo.mm"
include "unopbd.mm"
include "ax-mp.mm"
include "bdopf.mm"
include "hocofi.mm"
include "hosubcli.mm"
include "nmop0h.mm"
include "mpan2.mm"
include "0le0.mm"
include "00id.mm"
include "breqtrri.mm"
include "oveq12d.mm"
include "syl5breqr.mm"
include "eqbrtrd.mm"
include "wne.mm"
include "cmul.mm"
include "chos.mm"
include "honpncani.mm"
include "fveq2i.mm"
include "bdopcoi.mm"
include "bdophdi.mm"
include "nmoptrii.mm"
include "hocsubdiri.mm"
include "nmopcoi.mm"
include "eqbrtrri.mm"
include "clo.mm"
include "bdopln.mm"
include "hoddii.mm"
include "cr.mm"
include "nmopre.mm"
include "remulcli.mm"
include "le2addi.mm"
include "mp2an.mm"
include "bdophsi.mm"
include "readdcli.mm"
include "letri.mm"
include "c1.mm"
include "nmopun.mm"
include "oveq2d.mm"
include "recni.mm"
include "mulid1i.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "mulid2i.mm"
include "syl5breq.mm"
include "pm2.61ine.mm"

theorem unierri
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  assume unierr.1: |- F e. UniOp
  assume unierr.2: |- G e. UniOp
  assume unierr.3: |- S e. UniOp
  assume unierr.4: |- T e. UniOp


  assert |- ( normop ` ( ( F o. G ) -op ( S o. T ) ) ) <_ ( ( normop ` ( F -op S ) ) + ( normop ` ( G -op T ) ) )

  proof
    cF
    cG
    ccom
    #
    cS
    cT
    ccom
    #
    chod
    co
    #
    cnop
    cfv
    #
    cF
    cS
    chod
    co
    #
    cnop
    cfv
    #
    cG
    cT
    chod
    co
    #
    cnop
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    chil
    c0h
    chil
    c0h
    wceq
    #
    @3
    cc0
    @8
    cle
    @9
    chil
    chil
    @2
    wf
    @3
    cc0
    wceq
    @0
    @1
    cF
    cG
    cF
    cbo
    wcel
    #
    chil
    chil
    cF
    wf
    cF
    cuo
    wcel
    @10
    unierr.1
    cF
    unopbd
    ax-mp
    #
    cF
    bdopf
    ax-mp
    #
    cG
    cbo
    wcel
    #
    chil
    chil
    cG
    wf
    cG
    cuo
    wcel
    #
    @13
    unierr.2
    cG
    unopbd
    ax-mp
    #
    cG
    bdopf
    ax-mp
    #
    hocofi
    #
    cS
    cT
    cS
    cbo
    wcel
    #
    chil
    chil
    cS
    wf
    cS
    cuo
    wcel
    #
    @18
    unierr.3
    cS
    unopbd
    ax-mp
    #
    cS
    bdopf
    ax-mp
    #
    cT
    cbo
    wcel
    #
    chil
    chil
    cT
    wf
    cT
    cuo
    wcel
    @22
    unierr.4
    cT
    unopbd
    ax-mp
    #
    cT
    bdopf
    ax-mp
    #
    hocofi
    #
    hosubcli
    @2
    nmop0h
    mpan2
    @9
    cc0
    cc0
    cc0
    caddc
    co
    #
    @8
    cle
    cc0
    cc0
    @26
    cle
    0le0
    00id
    breqtrri
    @9
    @5
    cc0
    @7
    cc0
    caddc
    @9
    chil
    chil
    @4
    wf
    @5
    cc0
    wceq
    cF
    cS
    @12
    @21
    hosubcli
    @4
    nmop0h
    mpan2
    @9
    chil
    chil
    @6
    wf
    @7
    cc0
    wceq
    cG
    cT
    @16
    @24
    hosubcli
    @6
    nmop0h
    mpan2
    oveq12d
    syl5breqr
    eqbrtrd
    chil
    c0h
    wne
    #
    @3
    @5
    cG
    cnop
    cfv
    #
    cmul
    co
    #
    cS
    cnop
    cfv
    #
    @7
    cmul
    co
    #
    caddc
    co
    #
    @8
    cle
    @0
    cS
    cG
    ccom
    #
    chod
    co
    #
    @33
    @1
    chod
    co
    #
    chos
    co
    #
    cnop
    cfv
    #
    @3
    @32
    cle
    @36
    @2
    cnop
    @0
    @33
    @1
    @17
    cS
    cG
    @21
    @16
    hocofi
    @25
    honpncani
    fveq2i
    @37
    @34
    cnop
    cfv
    #
    @35
    cnop
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    @40
    @32
    cle
    wbr
    #
    @37
    @32
    cle
    wbr
    @34
    @35
    @0
    @33
    cF
    cG
    @11
    @15
    bdopcoi
    cS
    cG
    @20
    @15
    bdopcoi
    #
    bdophdi
    #
    @33
    @1
    @42
    cS
    cT
    @20
    @23
    bdopcoi
    bdophdi
    #
    nmoptrii
    @38
    @29
    cle
    wbr
    @39
    @31
    cle
    wbr
    @41
    @4
    cG
    ccom
    #
    cnop
    cfv
    @38
    @29
    cle
    @45
    @34
    cnop
    cF
    cS
    cG
    @12
    @21
    @16
    hocsubdiri
    fveq2i
    @4
    cG
    cF
    cS
    @11
    @20
    bdophdi
    #
    @15
    nmopcoi
    eqbrtrri
    cS
    @6
    ccom
    #
    cnop
    cfv
    @39
    @31
    cle
    @47
    @35
    cnop
    cS
    cG
    cT
    @18
    cS
    clo
    wcel
    @20
    cS
    bdopln
    ax-mp
    @16
    @24
    hoddii
    fveq2i
    cS
    @6
    @20
    cG
    cT
    @15
    @23
    bdophdi
    #
    nmopcoi
    eqbrtrri
    @38
    @39
    @29
    @31
    @34
    cbo
    wcel
    @38
    cr
    wcel
    @43
    @34
    nmopre
    ax-mp
    #
    @35
    cbo
    wcel
    @39
    cr
    wcel
    @44
    @35
    nmopre
    ax-mp
    #
    @5
    @28
    @4
    cbo
    wcel
    @5
    cr
    wcel
    @46
    @4
    nmopre
    ax-mp
    #
    @13
    @28
    cr
    wcel
    @15
    cG
    nmopre
    ax-mp
    remulcli
    #
    @30
    @7
    @18
    @30
    cr
    wcel
    @20
    cS
    nmopre
    ax-mp
    @6
    cbo
    wcel
    @7
    cr
    wcel
    @48
    @6
    nmopre
    ax-mp
    #
    remulcli
    #
    le2addi
    mp2an
    @37
    @40
    @32
    @36
    cbo
    wcel
    @37
    cr
    wcel
    @34
    @35
    @43
    @44
    bdophsi
    @36
    nmopre
    ax-mp
    @38
    @39
    @49
    @50
    readdcli
    @29
    @31
    @52
    @54
    readdcli
    letri
    mp2an
    eqbrtrri
    @27
    @29
    @5
    @31
    @7
    caddc
    @27
    @29
    @5
    c1
    cmul
    co
    @5
    @27
    @28
    c1
    @5
    cmul
    @27
    @14
    @28
    c1
    wceq
    unierr.2
    cG
    nmopun
    mpan2
    oveq2d
    @5
    @5
    @51
    recni
    mulid1i
    syl6eq
    @27
    @31
    c1
    @7
    cmul
    co
    @7
    @27
    @30
    c1
    @7
    cmul
    @27
    @19
    @30
    c1
    wceq
    unierr.3
    cS
    nmopun
    mpan2
    oveq1d
    @7
    @7
    @53
    recni
    mulid2i
    syl6eq
    oveq12d
    syl5breq
    pm2.61ine
end
