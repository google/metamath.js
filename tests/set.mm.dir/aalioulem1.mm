include "cdiv.mm"
include "co.mm"
include "cfv.mm"
include "cdgr.mm"
include "cexp.mm"
include "cmul.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "ccoe.mm"
include "csu.mm"
include "cz.mm"
include "cply.mm"
include "wcel.mm"
include "cc.mm"
include "wceq.mm"
include "zcnd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "eqid.mm"
include "coeid2.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "fzfid.mm"
include "cn0.mm"
include "dgrcl.mm"
include "syl.mm"
include "expcld.mm"
include "wa.mm"
include "wf.mm"
include "0z.mm"
include "coef2.mm"
include "sylancl.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "expcl.mm"
include "mulcld.mm"
include "fsummulc1.mm"
include "eqtrd.mm"
include "adantr.mm"
include "mulassd.mm"
include "wne.mm"
include "adantl.mm"
include "expdivd.mm"
include "cn.mm"
include "nnexpcl.mm"
include "div13d.mm"
include "cmin.mm"
include "elfzelz.mm"
include "nn0zd.mm"
include "expsubd.mm"
include "nnzd.mm"
include "fznn0sub.mm"
include "zexpcl.mm"
include "eqeltrrd.mm"
include "zmulcld.mm"
include "eqeltrd.mm"
include "fsumzcl.mm"

theorem aalioulem1
  let wph: wff ph
  let cF: class F
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume aalioulem1.a: |- ( ph -> F e. ( Poly ` ZZ ) )
  assume aalioulem1.b: |- ( ph -> X e. ZZ )
  assume aalioulem1.c: |- ( ph -> Y e. NN )


  assert |- ( ph -> ( ( F ` ( X / Y ) ) x. ( Y ^ ( deg ` F ) ) ) e. ZZ )

  proof
    wph
    cX
    cY
    cdiv
    co
    #
    cF
    cfv
    #
    cY
    cF
    cdgr
    cfv
    #
    cexp
    co
    #
    cmul
    co
    #
    cc0
    @2
    cfz
    co
    #
    va
    cv
    #
    cF
    ccoe
    cfv
    #
    cfv
    #
    @0
    @6
    cexp
    co
    #
    cmul
    co
    #
    @3
    cmul
    co
    #
    va
    csu
    #
    cz
    wph
    @4
    @5
    @10
    va
    csu
    #
    @3
    cmul
    co
    @12
    wph
    @1
    @13
    @3
    cmul
    wph
    cF
    cz
    cply
    cfv
    wcel
    #
    @0
    cc
    wcel
    #
    @1
    @13
    wceq
    aalioulem1.a
    wph
    cX
    cY
    wph
    cX
    aalioulem1.b
    zcnd
    wph
    cY
    aalioulem1.c
    nncnd
    #
    wph
    cY
    aalioulem1.c
    nnne0d
    #
    divcld
    #
    @7
    cz
    va
    cF
    @2
    @0
    @7
    eqid
    #
    @2
    eqid
    coeid2
    syl2anc
    oveq1d
    wph
    @5
    @10
    @3
    va
    wph
    cc0
    @2
    fzfid
    #
    wph
    cY
    @2
    @16
    wph
    @14
    @2
    cn0
    wcel
    #
    aalioulem1.a
    cz
    cF
    dgrcl
    syl
    #
    expcld
    wph
    @6
    @5
    wcel
    #
    wa
    #
    @8
    @9
    @24
    @8
    wph
    cn0
    cz
    @7
    wf
    #
    @6
    cn0
    wcel
    #
    @8
    cz
    wcel
    @23
    wph
    @14
    cc0
    cz
    wcel
    @25
    aalioulem1.a
    0z
    @7
    cz
    cF
    @19
    coef2
    sylancl
    @6
    @2
    elfznn0
    #
    cn0
    cz
    @6
    @7
    ffvelrn
    syl2an
    #
    zcnd
    #
    wph
    @15
    @26
    @9
    cc
    wcel
    @23
    @18
    @27
    @0
    @6
    expcl
    syl2an
    #
    mulcld
    fsummulc1
    eqtrd
    wph
    @5
    @11
    va
    @20
    @24
    @11
    @8
    @9
    @3
    cmul
    co
    #
    cmul
    co
    cz
    @24
    @8
    @9
    @3
    @29
    @30
    @24
    cY
    @2
    wph
    cY
    cc
    wcel
    @23
    @16
    adantr
    #
    wph
    @21
    @23
    @22
    adantr
    #
    expcld
    #
    mulassd
    @24
    @8
    @31
    @28
    @24
    @31
    @3
    cY
    @6
    cexp
    co
    #
    cdiv
    co
    #
    cX
    @6
    cexp
    co
    #
    cmul
    co
    #
    cz
    @24
    @31
    @37
    @35
    cdiv
    co
    #
    @3
    cmul
    co
    @38
    @24
    @9
    @39
    @3
    cmul
    @24
    cX
    cY
    @6
    @24
    cX
    wph
    cX
    cz
    wcel
    #
    @23
    aalioulem1.b
    adantr
    zcnd
    #
    @32
    wph
    cY
    cc0
    wne
    @23
    @17
    adantr
    #
    @23
    @26
    wph
    @27
    adantl
    #
    expdivd
    oveq1d
    @24
    @37
    @35
    @3
    @24
    cX
    @6
    @41
    @43
    expcld
    @24
    @35
    wph
    cY
    cn
    wcel
    #
    @26
    @35
    cn
    wcel
    @23
    aalioulem1.c
    @27
    cY
    @6
    nnexpcl
    syl2an
    #
    nncnd
    @34
    @24
    @35
    @45
    nnne0d
    div13d
    eqtrd
    @24
    @36
    @37
    @24
    cY
    @2
    @6
    cmin
    co
    #
    cexp
    co
    #
    @36
    cz
    @24
    cY
    @2
    @6
    @32
    @42
    @23
    @6
    cz
    wcel
    wph
    @6
    cc0
    @2
    elfzelz
    adantl
    @24
    @2
    @33
    nn0zd
    expsubd
    @24
    cY
    cz
    wcel
    @46
    cn0
    wcel
    #
    @47
    cz
    wcel
    @24
    cY
    wph
    @44
    @23
    aalioulem1.c
    adantr
    nnzd
    @23
    @48
    wph
    @6
    cc0
    @2
    fznn0sub
    adantl
    cY
    @46
    zexpcl
    syl2anc
    eqeltrrd
    wph
    @40
    @26
    @37
    cz
    wcel
    @23
    aalioulem1.b
    @27
    cX
    @6
    zexpcl
    syl2an
    zmulcld
    eqeltrd
    zmulcld
    eqeltrd
    fsumzcl
    eqeltrd
end
