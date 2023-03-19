include "c1.mm"
include "cneg.mm"
include "chash.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "cword.mm"
include "cn0.mm"
include "lencl.mm"
include "syl.mm"
include "nn0zd.mm"
include "m1expcl.mm"
include "zcnd.mm"
include "cc0.mm"
include "wne.mm"
include "cc.mm"
include "neg1cn.mm"
include "neg1ne0.mm"
include "expne0i.mm"
include "mp3an12.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmin.mm"
include "wceq.mm"
include "m1expaddsub.mm"
include "syl2anc.mm"
include "wa.mm"
include "expsub.mm"
include "mpanl12.mm"
include "eqtr3d.mm"
include "creverse.mm"
include "cconcat.mm"
include "revcl.mm"
include "ccatlen.mm"
include "revlen.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "ccatcl.mm"
include "cgsu.mm"
include "cplusg.mm"
include "c0g.mm"
include "cid.mm"
include "cres.mm"
include "cminusg.mm"
include "fveq2d.mm"
include "eqid.mm"
include "symgtrinv.mm"
include "eqtr2d.mm"
include "cgrp.mm"
include "cbs.mm"
include "symggrp.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "wss.mm"
include "symgtrf.mm"
include "sswrd.mm"
include "ax-mp.mm"
include "sseldi.mm"
include "gsumwcl.mm"
include "grprinv.mm"
include "gsumccat.mm"
include "syl3anc.mm"
include "symgid.mm"
include "3eqtr4d.mm"
include "psgnunilem4.mm"
include "diveq1d.mm"

theorem psgnuni
  let wph: wff ph
  let cD: class D
  let cT: class T
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  assume psgnuni.g: |- G = ( SymGrp ` D )
  assume psgnuni.t: |- T = ran ( pmTrsp ` D )
  assume psgnuni.d: |- ( ph -> D e. V )
  assume psgnuni.w: |- ( ph -> W e. Word T )
  assume psgnuni.x: |- ( ph -> X e. Word T )
  assume psgnuni.e: |- ( ph -> ( G gsum W ) = ( G gsum X ) )


  assert |- ( ph -> ( -u 1 ^ ( # ` W ) ) = ( -u 1 ^ ( # ` X ) ) )

  proof
    wph
    c1
    cneg
    #
    cW
    chash
    cfv
    #
    cexp
    co
    #
    @0
    cX
    chash
    cfv
    #
    cexp
    co
    #
    wph
    @2
    wph
    @1
    cz
    wcel
    #
    @2
    cz
    wcel
    wph
    @1
    wph
    cW
    cT
    cword
    #
    wcel
    #
    @1
    cn0
    wcel
    psgnuni.w
    cT
    cW
    lencl
    syl
    nn0zd
    #
    @1
    m1expcl
    syl
    zcnd
    wph
    @4
    wph
    @3
    cz
    wcel
    #
    @4
    cz
    wcel
    wph
    @3
    wph
    cX
    @6
    wcel
    #
    @3
    cn0
    wcel
    psgnuni.x
    cT
    cX
    lencl
    syl
    nn0zd
    #
    @3
    m1expcl
    syl
    zcnd
    wph
    @9
    @4
    cc0
    wne
    #
    @11
    @0
    cc
    wcel
    #
    @0
    cc0
    wne
    #
    @9
    @12
    neg1cn
    neg1ne0
    @0
    @3
    expne0i
    mp3an12
    syl
    wph
    @0
    @1
    @3
    caddc
    co
    #
    cexp
    co
    #
    @2
    @4
    cdiv
    co
    #
    c1
    wph
    @0
    @1
    @3
    cmin
    co
    cexp
    co
    #
    @16
    @17
    wph
    @5
    @9
    @18
    @16
    wceq
    @8
    @11
    @1
    @3
    m1expaddsub
    syl2anc
    wph
    @5
    @9
    @18
    @17
    wceq
    #
    @8
    @11
    @13
    @14
    @5
    @9
    wa
    @19
    neg1cn
    neg1ne0
    @0
    @1
    @3
    expsub
    mpanl12
    syl2anc
    eqtr3d
    wph
    @0
    cW
    cX
    creverse
    cfv
    #
    cconcat
    co
    #
    chash
    cfv
    #
    cexp
    co
    @16
    c1
    wph
    @22
    @15
    @0
    cexp
    wph
    @22
    @1
    @20
    chash
    cfv
    #
    caddc
    co
    #
    @15
    wph
    @7
    @20
    @6
    wcel
    #
    @22
    @24
    wceq
    psgnuni.w
    wph
    @10
    @25
    psgnuni.x
    cT
    cX
    revcl
    syl
    #
    cT
    cW
    @20
    ccatlen
    syl2anc
    wph
    @23
    @3
    @1
    caddc
    wph
    @10
    @23
    @3
    wceq
    psgnuni.x
    cT
    cX
    revlen
    syl
    oveq2d
    eqtrd
    oveq2d
    wph
    cD
    cT
    cG
    cV
    @21
    psgnuni.g
    psgnuni.t
    psgnuni.d
    wph
    @7
    @25
    @21
    @6
    wcel
    psgnuni.w
    @26
    cT
    cW
    @20
    ccatcl
    syl2anc
    wph
    cG
    cW
    cgsu
    co
    #
    cG
    @20
    cgsu
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cG
    c0g
    cfv
    #
    cG
    @21
    cgsu
    co
    #
    cid
    cD
    cres
    #
    wph
    @30
    @27
    @27
    cG
    cminusg
    cfv
    #
    cfv
    #
    @29
    co
    #
    @31
    wph
    @28
    @35
    @27
    @29
    wph
    @35
    cG
    cX
    cgsu
    co
    #
    @34
    cfv
    #
    @28
    wph
    @27
    @37
    @34
    psgnuni.e
    fveq2d
    wph
    cD
    cV
    wcel
    #
    @10
    @38
    @28
    wceq
    psgnuni.d
    psgnuni.x
    cD
    cT
    cG
    @34
    cV
    cX
    psgnuni.t
    psgnuni.g
    @34
    eqid
    #
    symgtrinv
    syl2anc
    eqtr2d
    oveq2d
    wph
    cG
    cgrp
    wcel
    #
    @27
    cG
    cbs
    cfv
    #
    wcel
    #
    @36
    @31
    wceq
    wph
    @39
    @41
    psgnuni.d
    cD
    cG
    cV
    psgnuni.g
    symggrp
    syl
    #
    wph
    cG
    cmnd
    wcel
    #
    cW
    @42
    cword
    #
    wcel
    #
    @43
    wph
    @41
    @45
    @44
    cG
    grpmnd
    syl
    #
    wph
    @6
    @46
    cW
    cT
    @42
    wss
    @6
    @46
    wss
    @42
    cD
    cT
    cG
    psgnuni.t
    psgnuni.g
    @42
    eqid
    #
    symgtrf
    cT
    @42
    sswrd
    ax-mp
    #
    psgnuni.w
    sseldi
    #
    @42
    cG
    cW
    @49
    gsumwcl
    syl2anc
    @42
    @29
    cG
    @34
    @27
    @31
    @49
    @29
    eqid
    #
    @31
    eqid
    @40
    grprinv
    syl2anc
    eqtrd
    wph
    @45
    @47
    @20
    @46
    wcel
    @32
    @30
    wceq
    @48
    @51
    wph
    @6
    @46
    @20
    @50
    @26
    sseldi
    @42
    @29
    cG
    cW
    @20
    @49
    @52
    gsumccat
    syl3anc
    wph
    @39
    @33
    @31
    wceq
    psgnuni.d
    cD
    cG
    cV
    psgnuni.g
    symgid
    syl
    3eqtr4d
    psgnunilem4
    eqtr3d
    eqtr3d
    diveq1d
end
