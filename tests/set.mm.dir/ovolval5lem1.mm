include "cn.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cmin.mm"
include "cioo.mm"
include "cvol.mm"
include "cfv.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cico.mm"
include "caddc.mm"
include "cxad.mm"
include "cvv.mm"
include "nfv.mm"
include "wcel.mm"
include "nnex.mm"
include "a1i.mm"
include "wa.mm"
include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "volf.mm"
include "ioombl.mm"
include "ffvelrnd.mm"
include "sge0xrclmpt.mm"
include "cxr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "cr.mm"
include "volicore.mm"
include "syl2anc.mm"
include "rpred.mm"
include "adantr.mm"
include "cn0.mm"
include "2nn.mm"
include "nnnn0.mm"
include "nnexpcl.mm"
include "nnred.mm"
include "adantl.mm"
include "wne.mm"
include "nnne0d.mm"
include "redivcld.mm"
include "readdcld.mm"
include "rexrd.mm"
include "cle.mm"
include "wbr.mm"
include "icombl.mm"
include "volge0.mm"
include "syl.mm"
include "crp.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "rpge0d.mm"
include "addge0d.mm"
include "rexr.mm"
include "ltpnf.mm"
include "xrltled.mm"
include "eliccxrd.mm"
include "xaddcld.mm"
include "cif.mm"
include "wceq.mm"
include "resubcld.mm"
include "volioore.mm"
include "iftrue.mm"
include "recnd.mm"
include "subsubd.mm"
include "3eqtrd.mm"
include "sublevolico.mm"
include "leadd1dd.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "iffalse.mm"
include "eqtrd.mm"
include "pm2.61dan.mm"
include "sge0lempt.mm"
include "rexaddd.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "fveq2d.mm"
include "sge0xadd.mm"
include "ltpnfd.mm"
include "elicod.mm"
include "sge0ad2en.mm"
include "oveq2d.mm"
include "xreqled.mm"
include "xrletrd.mm"

theorem ovolval5lem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vn: setvar n
  let cW: class W
  let vk: setvar k
  let vx: setvar x
  assume ovolval5lem1.a: |- ( ( ph /\ n e. NN ) -> A e. RR )
  assume ovolval5lem1.b: |- ( ( ph /\ n e. NN ) -> B e. RR )
  assume ovolval5lem1.w: |- ( ph -> W e. RR+ )
  assume ovolval5lem1.c: |- C = { n e. NN | A < B }

  disjoint C n
  disjoint W n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( n e. NN |-> ( vol ` ( ( A - ( W / ( 2 ^ n ) ) ) (,) B ) ) ) ) <_ ( ( sum^ ` ( n e. NN |-> ( vol ` ( A [,) B ) ) ) ) +e W ) )

  proof
    wph
    vn
    cn
    cA
    cW
    c2
    vn
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    cB
    cioo
    co
    #
    cvol
    cfv
    #
    cmpt
    csumge0
    cfv
    vn
    cn
    cA
    cB
    cico
    co
    #
    cvol
    cfv
    #
    @2
    caddc
    co
    #
    cmpt
    #
    csumge0
    cfv
    #
    vn
    cn
    @7
    cmpt
    csumge0
    cfv
    #
    cW
    cxad
    co
    #
    wph
    vn
    cn
    @5
    cvv
    wph
    vn
    nfv
    #
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    #
    wph
    @0
    cn
    wcel
    #
    wa
    #
    cvol
    cdm
    #
    cc0
    cpnf
    cicc
    co
    #
    @4
    cvol
    @17
    @18
    cvol
    wf
    @16
    volf
    a1i
    #
    @4
    @17
    wcel
    @16
    @3
    cB
    ioombl
    a1i
    ffvelrnd
    #
    sge0xrclmpt
    wph
    vn
    cn
    @8
    cvv
    @13
    @14
    @16
    cc0
    cpnf
    @8
    cc0
    cxr
    wcel
    #
    @16
    0xr
    a1i
    #
    cpnf
    cxr
    wcel
    #
    @16
    pnfxr
    a1i
    #
    @16
    @8
    @16
    @7
    @2
    @16
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @7
    cr
    wcel
    ovolval5lem1.a
    ovolval5lem1.b
    cA
    cB
    volicore
    syl2anc
    #
    @16
    cW
    @1
    wph
    cW
    cr
    wcel
    @15
    wph
    cW
    ovolval5lem1.w
    rpred
    #
    adantr
    @15
    @1
    cr
    wcel
    wph
    @15
    @1
    @15
    c2
    cn
    wcel
    #
    @0
    cn0
    wcel
    @1
    cn
    wcel
    @29
    @15
    2nn
    a1i
    @0
    nnnn0
    c2
    @0
    nnexpcl
    syl2anc
    #
    nnred
    adantl
    @15
    @1
    cc0
    wne
    wph
    @15
    @1
    @30
    nnne0d
    adantl
    redivcld
    #
    readdcld
    #
    rexrd
    @16
    @7
    @2
    @27
    @31
    @16
    @6
    @17
    wcel
    #
    cc0
    @7
    cle
    wbr
    @16
    @25
    cB
    cxr
    wcel
    @33
    ovolval5lem1.a
    @16
    cB
    ovolval5lem1.b
    rexrd
    cA
    cB
    icombl
    syl2anc
    #
    @6
    volge0
    syl
    @16
    @2
    @16
    cW
    @1
    wph
    cW
    crp
    wcel
    @15
    ovolval5lem1.w
    adantr
    @15
    @1
    crp
    wcel
    wph
    @15
    @1
    @30
    nnrpd
    adantl
    rpdivcld
    rpge0d
    #
    addge0d
    #
    @16
    @8
    cr
    wcel
    #
    @8
    cpnf
    cle
    wbr
    @32
    @37
    @8
    cpnf
    @8
    rexr
    @23
    @37
    pnfxr
    a1i
    @8
    ltpnf
    xrltled
    syl
    eliccxrd
    #
    sge0xrclmpt
    #
    wph
    @11
    cW
    wph
    vn
    cn
    @7
    cvv
    @13
    @14
    @16
    @17
    @18
    @6
    cvol
    @19
    @34
    ffvelrnd
    #
    sge0xrclmpt
    wph
    cW
    @28
    rexrd
    #
    xaddcld
    wph
    vn
    cn
    @5
    @8
    cvv
    @13
    @14
    @20
    @38
    @16
    @3
    cB
    cle
    wbr
    #
    @5
    @8
    cle
    wbr
    @16
    @42
    wa
    #
    @5
    cB
    cA
    cmin
    co
    #
    @2
    caddc
    co
    #
    @8
    cle
    @43
    @5
    @42
    cB
    @3
    cmin
    co
    #
    cc0
    cif
    #
    @46
    @45
    @16
    @5
    @47
    wceq
    #
    @42
    @16
    @3
    cr
    wcel
    @26
    @48
    @16
    cA
    @2
    ovolval5lem1.a
    @31
    resubcld
    ovolval5lem1.b
    @3
    cB
    volioore
    syl2anc
    #
    adantr
    @42
    @47
    @46
    wceq
    @16
    @42
    @46
    cc0
    iftrue
    adantl
    @16
    @46
    @45
    wceq
    @42
    @16
    cB
    cA
    @2
    @16
    cB
    ovolval5lem1.b
    recnd
    @16
    cA
    ovolval5lem1.a
    recnd
    @16
    @2
    @31
    recnd
    subsubd
    adantr
    3eqtrd
    @16
    @45
    @8
    cle
    wbr
    @42
    @16
    @44
    @7
    @2
    @16
    cB
    cA
    ovolval5lem1.b
    ovolval5lem1.a
    resubcld
    @27
    @31
    @16
    cA
    cB
    ovolval5lem1.a
    ovolval5lem1.b
    sublevolico
    leadd1dd
    adantr
    eqbrtrd
    @16
    @42
    wn
    #
    wa
    #
    @5
    cc0
    @8
    cle
    @51
    @5
    @47
    cc0
    @16
    @48
    @50
    @49
    adantr
    @50
    @47
    cc0
    wceq
    @16
    @42
    @46
    cc0
    iffalse
    adantl
    eqtrd
    @16
    cc0
    @8
    cle
    wbr
    @50
    @36
    adantr
    eqbrtrd
    pm2.61dan
    sge0lempt
    wph
    @10
    @12
    @39
    wph
    @10
    vn
    cn
    @7
    @2
    cxad
    co
    #
    cmpt
    #
    csumge0
    cfv
    @11
    vn
    cn
    @2
    cmpt
    csumge0
    cfv
    #
    cxad
    co
    @12
    wph
    @9
    @53
    csumge0
    wph
    vn
    cn
    @8
    @52
    @16
    @52
    @8
    @16
    @7
    @2
    @27
    @31
    rexaddd
    eqcomd
    mpteq2dva
    fveq2d
    wph
    cn
    @7
    @2
    vn
    cvv
    @13
    @14
    @40
    @16
    cc0
    cpnf
    @2
    @22
    @24
    @16
    @2
    @31
    rexrd
    @35
    @16
    @2
    cr
    wcel
    #
    @2
    cpnf
    cle
    wbr
    @31
    @55
    @2
    cpnf
    @2
    rexr
    @23
    @55
    pnfxr
    a1i
    @2
    ltpnf
    xrltled
    syl
    eliccxrd
    sge0xadd
    wph
    @54
    cW
    @11
    cxad
    wph
    cW
    vn
    wph
    cc0
    cpnf
    cW
    @21
    wph
    0xr
    a1i
    @23
    wph
    pnfxr
    a1i
    @41
    wph
    cW
    ovolval5lem1.w
    rpge0d
    wph
    cW
    @28
    ltpnfd
    elicod
    sge0ad2en
    oveq2d
    3eqtrd
    xreqled
    xrletrd
end
