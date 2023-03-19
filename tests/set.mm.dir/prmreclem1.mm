include "cn.mm"
include "wcel.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cuz.mm"
include "cdiv.mm"
include "wn.mm"
include "wi.mm"
include "cv.mm"
include "crab.mm"
include "ssrab2.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "supeq1d.mm"
include "ltso.mm"
include "supex.mm"
include "fvmpt.mm"
include "cz.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wral.mm"
include "wrex.mm"
include "nnssz.mm"
include "sstri.mm"
include "a1i.mm"
include "c1.mm"
include "1nn.mm"
include "nnz.mm"
include "1dvds.mm"
include "syl.mm"
include "oveq1.mm"
include "sq1.mm"
include "syl6eq.mm"
include "breq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "wa.mm"
include "zsqcl.mm"
include "id.mm"
include "dvdsle.mm"
include "syl2anr.mm"
include "nnlesq.mm"
include "adantl.mm"
include "nnre.mm"
include "resqcld.mm"
include "adantr.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "syld.mm"
include "ralrimiva.mm"
include "ralrab.mm"
include "sylibr.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "suprzcl2.mm"
include "eqeltrd.mm"
include "sseldi.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "sylib.mm"
include "simprd.mm"
include "cmul.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "cc0.mm"
include "wb.mm"
include "1red.mm"
include "eluz2nn.mm"
include "nnred.mm"
include "nngt0d.mm"
include "ltmul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "nnmulcl.mm"
include "syl2an.mm"
include "ltnled.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "nnsqcld.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "dvdscmul.mm"
include "mpd.mm"
include "cc.mm"
include "sqmuld.mm"
include "eqcomd.mm"
include "nncn.mm"
include "divcan2d.mm"
include "3brtr3d.mm"
include "suprzub.mm"
include "breqtrrd.mm"
include "mtand.mm"
include "ex.mm"
include "3jca.mm"

theorem prmreclem1
  let cQ: class Q
  let vn: setvar n
  let cK: class K
  let cN: class N
  let vr: setvar r
  let vx: setvar x
  let vz: setvar z
  assume prmreclem1.1: |- Q = ( n e. NN |-> sup ( { r e. NN | ( r ^ 2 ) || n } , RR , < ) )

  disjoint K r
  disjoint n r
  disjoint N n
  disjoint N r
  disjoint Q r
  disjoint r x
  disjoint K x
  disjoint n x
  disjoint n z
  disjoint r z
  disjoint x z
  disjoint N x
  disjoint N z
  disjoint Q x
  disjoint Q z
  assert |- ( N e. NN -> ( ( Q ` N ) e. NN /\ ( ( Q ` N ) ^ 2 ) || N /\ ( K e. ( ZZ>= ` 2 ) -> -. ( K ^ 2 ) || ( N / ( ( Q ` N ) ^ 2 ) ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cQ
    cfv
    #
    cn
    wcel
    #
    @1
    c2
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    cK
    c2
    cuz
    cfv
    wcel
    #
    cK
    c2
    cexp
    co
    #
    cN
    @3
    cdiv
    co
    #
    cdvds
    wbr
    #
    wn
    #
    wi
    @0
    vr
    cv
    #
    c2
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    vr
    cn
    crab
    #
    cn
    @1
    @12
    vr
    cn
    ssrab2
    #
    @0
    @1
    @13
    cr
    clt
    csup
    #
    @13
    vn
    cN
    @11
    vn
    cv
    #
    cdvds
    wbr
    #
    vr
    cn
    crab
    #
    cr
    clt
    csup
    @15
    cn
    cQ
    @16
    cN
    wceq
    #
    cr
    @18
    @13
    clt
    @19
    @17
    @12
    vr
    cn
    @16
    cN
    @11
    cdvds
    breq2
    rabbidv
    supeq1d
    prmreclem1.1
    cr
    @13
    clt
    ltso
    supex
    fvmpt
    #
    @0
    @13
    cz
    wss
    #
    @13
    c0
    wne
    #
    vz
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vz
    @13
    wral
    #
    vx
    cz
    wrex
    #
    @15
    @13
    wcel
    @21
    @0
    @13
    cn
    cz
    @14
    nnssz
    sstri
    #
    a1i
    @0
    c1
    @13
    wcel
    #
    @22
    @0
    c1
    cn
    wcel
    #
    c1
    cN
    cdvds
    wbr
    #
    @29
    @30
    @0
    1nn
    a1i
    @0
    cN
    cz
    wcel
    #
    @31
    cN
    nnz
    #
    cN
    1dvds
    syl
    @12
    @31
    vr
    c1
    cn
    @10
    c1
    wceq
    #
    @11
    c1
    cN
    cdvds
    @34
    @11
    c1
    c2
    cexp
    co
    c1
    @10
    c1
    c2
    cexp
    oveq1
    sq1
    syl6eq
    breq1d
    elrab
    sylanbrc
    @13
    c1
    ne0i
    syl
    @0
    @32
    @23
    cN
    cle
    wbr
    #
    vz
    @13
    wral
    #
    @27
    @33
    @0
    @23
    c2
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    @35
    wi
    #
    vz
    cn
    wral
    @36
    @0
    @39
    vz
    cn
    @0
    @23
    cn
    wcel
    #
    wa
    #
    @38
    @37
    cN
    cle
    wbr
    #
    @35
    @40
    @37
    cz
    wcel
    #
    @0
    @38
    @42
    wi
    @0
    @40
    @23
    cz
    wcel
    @43
    @23
    nnz
    @23
    zsqcl
    syl
    @0
    id
    @37
    cN
    dvdsle
    syl2anr
    @41
    @23
    @37
    cle
    wbr
    #
    @42
    @35
    @40
    @44
    @0
    @23
    nnlesq
    adantl
    @41
    @23
    cr
    wcel
    #
    @37
    cr
    wcel
    cN
    cr
    wcel
    #
    @44
    @42
    wa
    @35
    wi
    @40
    @45
    @0
    @23
    nnre
    adantl
    #
    @41
    @23
    @47
    resqcld
    @0
    @46
    @40
    cN
    nnre
    adantr
    @23
    @37
    cN
    letr
    syl3anc
    mpand
    syld
    ralrimiva
    @12
    @38
    @35
    vz
    vr
    cn
    @10
    @23
    wceq
    @11
    @37
    cN
    cdvds
    @10
    @23
    c2
    cexp
    oveq1
    breq1d
    #
    ralrab
    sylibr
    @26
    @36
    vx
    cN
    cz
    @24
    cN
    wceq
    @25
    @35
    vz
    @13
    @24
    cN
    @23
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    vx
    vz
    @13
    suprzcl2
    syl3anc
    eqeltrd
    #
    sseldi
    #
    @0
    @2
    @4
    @0
    @1
    @13
    wcel
    @2
    @4
    wa
    @50
    @38
    @4
    vz
    @1
    cn
    @13
    @23
    @1
    wceq
    @37
    @3
    cN
    cdvds
    @23
    @1
    c2
    cexp
    oveq1
    breq1d
    @12
    @38
    vr
    vz
    cn
    @48
    cbvrabv
    elrab2
    sylib
    simprd
    #
    @0
    @5
    @9
    @0
    @5
    wa
    #
    @8
    @1
    cK
    cmul
    co
    #
    @1
    cle
    wbr
    #
    @53
    @1
    @54
    clt
    wbr
    @55
    wn
    @53
    @1
    c1
    cmul
    co
    #
    @1
    @54
    clt
    @53
    @1
    @53
    @1
    @0
    @2
    @5
    @51
    adantr
    #
    nncnd
    #
    mulid1d
    @53
    c1
    cK
    clt
    wbr
    #
    @56
    @54
    clt
    wbr
    #
    @5
    @59
    @0
    @5
    cK
    cn
    wcel
    #
    @59
    cK
    eluz2b2
    simprbi
    adantl
    @53
    c1
    cr
    wcel
    cK
    cr
    wcel
    @1
    cr
    wcel
    cc0
    @1
    clt
    wbr
    @59
    @60
    wb
    @53
    1red
    @53
    cK
    @5
    @61
    @0
    cK
    eluz2nn
    #
    adantl
    #
    nnred
    @53
    @1
    @57
    nnred
    #
    @53
    @1
    @57
    nngt0d
    c1
    cK
    @1
    ltmul2
    syl112anc
    mpbid
    eqbrtrrd
    @53
    @1
    @54
    @64
    @53
    @54
    @0
    @2
    @61
    @54
    cn
    wcel
    #
    @5
    @51
    @62
    @1
    cK
    nnmulcl
    syl2an
    #
    nnred
    ltnled
    mpbid
    @53
    @8
    wa
    #
    @54
    @15
    @1
    cle
    @67
    @21
    @27
    @54
    @13
    wcel
    #
    @54
    @15
    cle
    wbr
    @21
    @67
    @28
    a1i
    @0
    @27
    @5
    @8
    @49
    ad2antrr
    @67
    @65
    @54
    c2
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    @68
    @53
    @65
    @8
    @66
    adantr
    @67
    @3
    @6
    cmul
    co
    #
    @3
    @7
    cmul
    co
    #
    @69
    cN
    cdvds
    @67
    @8
    @71
    @72
    cdvds
    wbr
    #
    @53
    @8
    simpr
    @67
    @6
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    @8
    @73
    wi
    @67
    @6
    cn
    wcel
    @74
    @67
    cK
    @53
    @61
    @8
    @63
    adantr
    #
    nnsqcld
    @6
    nnz
    syl
    @0
    @75
    @5
    @8
    @0
    @4
    @75
    @52
    @0
    @76
    @3
    cc0
    wne
    #
    @32
    @4
    @75
    wb
    @0
    cn
    cz
    @3
    nnssz
    @0
    @1
    @51
    nnsqcld
    #
    sseldi
    #
    @0
    @3
    @79
    nnne0d
    #
    @33
    @3
    cN
    dvdsval2
    syl3anc
    mpbid
    ad2antrr
    @0
    @76
    @5
    @8
    @80
    ad2antrr
    @3
    @6
    @7
    dvdscmul
    syl3anc
    mpd
    @67
    @69
    @71
    @67
    @1
    cK
    @53
    @1
    cc
    wcel
    @8
    @58
    adantr
    @67
    cK
    @77
    nncnd
    sqmuld
    eqcomd
    @67
    cN
    @3
    @0
    cN
    cc
    wcel
    @5
    @8
    cN
    nncn
    ad2antrr
    @67
    @3
    @0
    @3
    cn
    wcel
    @5
    @8
    @79
    ad2antrr
    nncnd
    @0
    @78
    @5
    @8
    @81
    ad2antrr
    divcan2d
    3brtr3d
    @12
    @70
    vr
    @54
    cn
    @10
    @54
    wceq
    @11
    @69
    cN
    cdvds
    @10
    @54
    c2
    cexp
    oveq1
    breq1d
    elrab
    sylanbrc
    vx
    vz
    @13
    @54
    suprzub
    syl3anc
    @0
    @1
    @15
    wceq
    @5
    @8
    @20
    ad2antrr
    breqtrrd
    mtand
    ex
    3jca
end
