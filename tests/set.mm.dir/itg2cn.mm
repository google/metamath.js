include "cr.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "wn.mm"
include "cvol.mm"
include "clt.mm"
include "wcel.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cn.mm"
include "rphalfcld.mm"
include "ltsubrpd.mm"
include "rpred.mm"
include "resubcld.mm"
include "ltnled.mm"
include "mpbid.mm"
include "crn.mm"
include "cxr.mm"
include "csup.mm"
include "wss.mm"
include "wb.mm"
include "wf.mm"
include "wa.mm"
include "cpnf.mm"
include "cicc.mm"
include "cico.mm"
include "ffvelrnda.mm"
include "elrege0.mm"
include "sylib.mm"
include "simpld.mm"
include "rexrd.mm"
include "simprd.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "0e0iccpnf.mm"
include "ifcl.mm"
include "sylancl.mm"
include "adantlr.mm"
include "eqid.mm"
include "fmptd.mm"
include "itg2cl.mm"
include "syl.mm"
include "frn.mm"
include "supxrleub.mm"
include "syl2anc.mm"
include "itg2cnlem1.mm"
include "breq1d.mm"
include "wfn.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "weq.mm"
include "breq2.mm"
include "ifbid.mm"
include "mpteq2dv.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ralbiia.mm"
include "syl6bb.mm"
include "3bitr3d.mm"
include "mtbid.mm"
include "rexnal.mm"
include "sylibr.mm"
include "adantr.mm"
include "cmbf.mm"
include "simprl.mm"
include "simprr.mm"
include "fveq2.mm"
include "ifbieq1d.mm"
include "cbvmptv.mm"
include "fveq2i.mm"
include "breq1i.mm"
include "sylnib.mm"
include "itg2cnlem2.mm"
include "elequ1.mm"
include "imbi2i.mm"
include "ralbii.mm"
include "rexbii.mm"
include "rexlimddv.mm"

theorem itg2cn
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cC: class C
  let cF: class F
  let vd: setvar d
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let vn: setvar n
  let vw: setvar w
  let cM: class M
  assume itg2cn.1: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume itg2cn.2: |- ( ph -> F e. MblFn )
  assume itg2cn.3: |- ( ph -> ( S.2 ` F ) e. RR )
  assume itg2cn.4: |- ( ph -> C e. RR+ )

  disjoint d u
  disjoint d x
  disjoint C d
  disjoint u x
  disjoint C u
  disjoint C x
  disjoint F d
  disjoint F u
  disjoint F x
  disjoint ph u
  disjoint ph x
  disjoint d m
  disjoint d y
  disjoint d z
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint C m
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint d n
  disjoint d w
  disjoint m n
  disjoint m w
  disjoint F m
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint ph z
  disjoint M d
  disjoint M u
  disjoint M x
  assert |- ( ph -> E. d e. RR+ A. u e. dom vol ( ( vol ` u ) < d -> ( S.2 ` ( x e. RR |-> if ( x e. u , ( F ` x ) , 0 ) ) ) < C ) )

  proof
    wph
    vx
    cr
    vx
    cv
    #
    cF
    cfv
    #
    vm
    cv
    #
    cle
    wbr
    #
    @1
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cF
    citg2
    cfv
    #
    cC
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cle
    wbr
    #
    wn
    #
    vu
    cv
    #
    cvol
    cfv
    vd
    cv
    clt
    wbr
    #
    vx
    cr
    @0
    @12
    wcel
    #
    @1
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cC
    clt
    wbr
    #
    wi
    #
    vu
    cvol
    cdm
    #
    wral
    #
    vd
    crp
    wrex
    #
    vm
    cn
    wph
    @10
    vm
    cn
    wral
    #
    wn
    @11
    vm
    cn
    wrex
    wph
    @7
    @9
    cle
    wbr
    #
    @23
    wph
    @9
    @7
    clt
    wbr
    @24
    wn
    wph
    @7
    @8
    itg2cn.3
    wph
    cC
    itg2cn.4
    rphalfcld
    #
    ltsubrpd
    wph
    @9
    @7
    wph
    @7
    @8
    itg2cn.3
    wph
    @8
    @25
    rpred
    resubcld
    #
    itg2cn.3
    ltnled
    mpbid
    wph
    vn
    cn
    vx
    cr
    @1
    vn
    cv
    #
    cle
    wbr
    #
    @1
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    @9
    cle
    wbr
    #
    vz
    cv
    #
    @9
    cle
    wbr
    #
    vz
    @33
    wral
    #
    @24
    @23
    wph
    @33
    cxr
    wss
    #
    @9
    cxr
    wcel
    @35
    @38
    wb
    wph
    cn
    cxr
    @32
    wf
    #
    @39
    wph
    vn
    cn
    @31
    cxr
    @32
    wph
    @27
    cn
    wcel
    #
    wa
    #
    cr
    cc0
    cpnf
    cicc
    co
    #
    @30
    wf
    @31
    cxr
    wcel
    @42
    vx
    cr
    @29
    @43
    @30
    wph
    @0
    cr
    wcel
    #
    @29
    @43
    wcel
    #
    @41
    wph
    @44
    wa
    #
    @1
    @43
    wcel
    #
    cc0
    @43
    wcel
    @45
    @46
    @1
    cxr
    wcel
    cc0
    @1
    cle
    wbr
    #
    @47
    @46
    @1
    @46
    @1
    cr
    wcel
    #
    @48
    @46
    @1
    cc0
    cpnf
    cico
    co
    #
    wcel
    @49
    @48
    wa
    wph
    cr
    @50
    @0
    cF
    itg2cn.1
    ffvelrnda
    @1
    elrege0
    sylib
    #
    simpld
    rexrd
    @46
    @49
    @48
    @51
    simprd
    @1
    elxrge0
    sylanbrc
    0e0iccpnf
    @28
    @1
    cc0
    @43
    ifcl
    sylancl
    adantlr
    @30
    eqid
    fmptd
    @30
    itg2cl
    syl
    @32
    eqid
    #
    fmptd
    #
    cn
    cxr
    @32
    frn
    syl
    wph
    @9
    @26
    rexrd
    vz
    @33
    @9
    supxrleub
    syl2anc
    wph
    @34
    @7
    @9
    cle
    wph
    vx
    vn
    cF
    itg2cn.1
    itg2cn.2
    itg2cn.3
    itg2cnlem1
    breq1d
    wph
    @32
    cn
    wfn
    #
    @38
    @23
    wb
    wph
    @40
    @54
    @53
    cn
    cxr
    @32
    ffn
    syl
    @54
    @38
    @2
    @32
    cfv
    #
    @9
    cle
    wbr
    #
    vm
    cn
    wral
    @23
    @37
    @56
    vz
    vm
    cn
    @32
    @36
    @55
    @9
    cle
    breq1
    ralrn
    @56
    @10
    vm
    cn
    @2
    cn
    wcel
    #
    @55
    @6
    @9
    cle
    vn
    @2
    @31
    @6
    cn
    @32
    vn
    vm
    weq
    #
    @30
    @5
    citg2
    @58
    vx
    cr
    @29
    @4
    @58
    @28
    @3
    @1
    cc0
    @27
    @2
    @1
    cle
    breq2
    ifbid
    mpteq2dv
    fveq2d
    @52
    @5
    citg2
    fvex
    fvmpt
    breq1d
    ralbiia
    syl6bb
    syl
    3bitr3d
    mtbid
    @10
    vm
    cn
    rexnal
    sylibr
    wph
    @57
    @11
    wa
    #
    wa
    #
    @13
    vy
    cr
    vy
    cv
    #
    @12
    wcel
    #
    @61
    cF
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cC
    clt
    wbr
    #
    wi
    #
    vu
    @20
    wral
    #
    vd
    crp
    wrex
    @22
    @60
    vy
    vu
    cC
    cF
    @2
    vd
    wph
    cr
    @50
    cF
    wf
    @59
    itg2cn.1
    adantr
    wph
    cF
    cmbf
    wcel
    @59
    itg2cn.2
    adantr
    wph
    @7
    cr
    wcel
    @59
    itg2cn.3
    adantr
    wph
    cC
    crp
    wcel
    @59
    itg2cn.4
    adantr
    wph
    @57
    @11
    simprl
    @60
    @10
    vy
    cr
    @63
    @2
    cle
    wbr
    #
    @63
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @9
    cle
    wbr
    wph
    @57
    @11
    simprr
    @6
    @73
    @9
    cle
    @5
    @72
    citg2
    vx
    vy
    cr
    @4
    @71
    vx
    vy
    weq
    #
    @3
    @70
    @1
    @63
    cc0
    @74
    @1
    @63
    @2
    cle
    @0
    @61
    cF
    fveq2
    #
    breq1d
    @75
    ifbieq1d
    cbvmptv
    fveq2i
    breq1i
    sylnib
    itg2cnlem2
    @21
    @69
    vd
    crp
    @19
    @68
    vu
    @20
    @18
    @67
    @13
    @17
    @66
    cC
    clt
    @16
    @65
    citg2
    vx
    vy
    cr
    @15
    @64
    @74
    @14
    @62
    @1
    @63
    cc0
    vx
    vy
    vu
    elequ1
    @75
    ifbieq1d
    cbvmptv
    fveq2i
    breq1i
    imbi2i
    ralbii
    rexbii
    sylibr
    rexlimddv
end
