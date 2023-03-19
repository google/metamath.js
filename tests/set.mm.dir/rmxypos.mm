include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cc0.mm"
include "crmx.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "crmy.mm"
include "cle.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "0lt1.mm"
include "rmx0.mm"
include "syl5breqr.mm"
include "0le0.mm"
include "rmy0.mm"
include "jca.mm"
include "w3a.mm"
include "cmul.mm"
include "cexp.mm"
include "cmin.mm"
include "cr.mm"
include "cz.mm"
include "simp2.mm"
include "nn0z.mm"
include "3ad2ant1.mm"
include "frmx.mm"
include "fovcl.mm"
include "syl2anc.mm"
include "nn0red.mm"
include "eluzelre.mm"
include "3ad2ant2.mm"
include "remulcld.mm"
include "rmspecpos.mm"
include "rpred.mm"
include "frmy.mm"
include "zred.mm"
include "simp3l.mm"
include "eluz2nn.mm"
include "nngt0d.mm"
include "mulgt0d.mm"
include "rpge0d.mm"
include "simp3r.mm"
include "mulge0d.mm"
include "addgtge0.mm"
include "syl22anc.mm"
include "rmxp1.mm"
include "breqtrrd.mm"
include "eluzge2nn0.mm"
include "nn0ge0d.mm"
include "addge0d.mm"
include "rmyp1.mm"
include "3exp.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem rmxypos
  let cA: class A
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( 0 < ( A rmX N ) /\ 0 <_ ( A rmY N ) ) )

  proof
    cN
    cn0
    wcel
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cc0
    cA
    cN
    crmx
    co
    #
    clt
    wbr
    #
    cc0
    cA
    cN
    crmy
    co
    #
    cle
    wbr
    #
    wa
    #
    @1
    cc0
    cA
    va
    cv
    #
    crmx
    co
    #
    clt
    wbr
    #
    cc0
    cA
    @7
    crmy
    co
    #
    cle
    wbr
    #
    wa
    #
    wi
    @1
    cc0
    cA
    cc0
    crmx
    co
    #
    clt
    wbr
    #
    cc0
    cA
    cc0
    crmy
    co
    #
    cle
    wbr
    #
    wa
    #
    wi
    @1
    cc0
    cA
    vb
    cv
    #
    crmx
    co
    #
    clt
    wbr
    #
    cc0
    cA
    @18
    crmy
    co
    #
    cle
    wbr
    #
    wa
    #
    wi
    @1
    cc0
    cA
    @18
    c1
    caddc
    co
    #
    crmx
    co
    #
    clt
    wbr
    #
    cc0
    cA
    @24
    crmy
    co
    #
    cle
    wbr
    #
    wa
    #
    wi
    @1
    @6
    wi
    va
    vb
    cN
    @7
    cc0
    wceq
    #
    @12
    @17
    @1
    @30
    @9
    @14
    @11
    @16
    @30
    @8
    @13
    cc0
    clt
    @7
    cc0
    cA
    crmx
    oveq2
    breq2d
    @30
    @10
    @15
    cc0
    cle
    @7
    cc0
    cA
    crmy
    oveq2
    breq2d
    anbi12d
    imbi2d
    va
    vb
    weq
    #
    @12
    @23
    @1
    @31
    @9
    @20
    @11
    @22
    @31
    @8
    @19
    cc0
    clt
    @7
    @18
    cA
    crmx
    oveq2
    breq2d
    @31
    @10
    @21
    cc0
    cle
    @7
    @18
    cA
    crmy
    oveq2
    breq2d
    anbi12d
    imbi2d
    @7
    @24
    wceq
    #
    @12
    @29
    @1
    @32
    @9
    @26
    @11
    @28
    @32
    @8
    @25
    cc0
    clt
    @7
    @24
    cA
    crmx
    oveq2
    breq2d
    @32
    @10
    @27
    cc0
    cle
    @7
    @24
    cA
    crmy
    oveq2
    breq2d
    anbi12d
    imbi2d
    @7
    cN
    wceq
    #
    @12
    @6
    @1
    @33
    @9
    @3
    @11
    @5
    @33
    @8
    @2
    cc0
    clt
    @7
    cN
    cA
    crmx
    oveq2
    breq2d
    @33
    @10
    @4
    cc0
    cle
    @7
    cN
    cA
    crmy
    oveq2
    breq2d
    anbi12d
    imbi2d
    @1
    @14
    @16
    @1
    cc0
    c1
    @13
    clt
    0lt1
    cA
    rmx0
    syl5breqr
    @1
    cc0
    cc0
    @15
    cle
    0le0
    cA
    rmy0
    syl5breqr
    jca
    @18
    cn0
    wcel
    #
    @1
    @23
    @29
    @34
    @1
    @23
    @29
    @34
    @1
    @23
    w3a
    #
    @26
    @28
    @35
    cc0
    @19
    cA
    cmul
    co
    #
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    #
    @21
    cmul
    co
    #
    caddc
    co
    #
    @25
    clt
    @35
    @36
    cr
    wcel
    @38
    cr
    wcel
    cc0
    @36
    clt
    wbr
    cc0
    @38
    cle
    wbr
    cc0
    @39
    clt
    wbr
    @35
    @19
    cA
    @35
    @19
    @35
    @1
    @18
    cz
    wcel
    #
    @19
    cn0
    wcel
    @34
    @1
    @23
    simp2
    #
    @34
    @1
    @40
    @23
    @18
    nn0z
    3ad2ant1
    #
    cA
    @18
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    syl2anc
    #
    nn0red
    #
    @1
    @34
    cA
    cr
    wcel
    @23
    c2
    cA
    eluzelre
    3ad2ant2
    #
    remulcld
    @35
    @37
    @21
    @1
    @34
    @37
    cr
    wcel
    @23
    @1
    @37
    cA
    rmspecpos
    #
    rpred
    3ad2ant2
    #
    @35
    @21
    @35
    @1
    @40
    @21
    cz
    wcel
    @41
    @42
    cA
    @18
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    zred
    #
    remulcld
    @35
    @19
    cA
    @44
    @45
    @34
    @1
    @20
    @22
    simp3l
    @1
    @34
    cc0
    cA
    clt
    wbr
    @23
    @1
    cA
    cA
    eluz2nn
    nngt0d
    3ad2ant2
    mulgt0d
    @35
    @37
    @21
    @47
    @48
    @1
    @34
    cc0
    @37
    cle
    wbr
    @23
    @1
    @37
    @46
    rpge0d
    3ad2ant2
    @34
    @1
    @20
    @22
    simp3r
    #
    mulge0d
    @36
    @38
    addgtge0
    syl22anc
    @35
    @1
    @40
    @25
    @39
    wceq
    @41
    @42
    cA
    @18
    rmxp1
    syl2anc
    breqtrrd
    @35
    cc0
    @21
    cA
    cmul
    co
    #
    @19
    caddc
    co
    #
    @27
    cle
    @35
    @50
    @19
    @35
    @21
    cA
    @48
    @45
    remulcld
    @44
    @35
    @21
    cA
    @48
    @45
    @49
    @1
    @34
    cc0
    cA
    cle
    wbr
    @23
    @1
    cA
    cA
    eluzge2nn0
    nn0ge0d
    3ad2ant2
    mulge0d
    @35
    @19
    @43
    nn0ge0d
    addge0d
    @35
    @1
    @40
    @27
    @51
    wceq
    @41
    @42
    cA
    @18
    rmyp1
    syl2anc
    breqtrrd
    jca
    3exp
    a2d
    nn0ind
    impcom
end
