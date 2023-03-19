include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "covoln.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cle.mm"
include "wbr.mm"
include "cun.mm"
include "cxad.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "c0.mm"
include "cif.mm"
include "cr.mm"
include "cmap.mm"
include "cpw.mm"
include "wcel.mm"
include "wa.mm"
include "iftrue.mm"
include "adantl.mm"
include "cvv.mm"
include "ovexd.mm"
include "ssexd.mm"
include "elpwd.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "wn.mm"
include "simpl.mm"
include "iffalsed.mm"
include "simpr.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "adantll.mm"
include "ad2antrr.mm"
include "adantllr.mm"
include "0elpw.mm"
include "a1i.mm"
include "pm2.61dan.mm"
include "fmptd.mm"
include "ovnsubadd.mm"
include "cpr.mm"
include "cdif.mm"
include "wral.mm"
include "eldifi.mm"
include "eldifn.mm"
include "vex.mm"
include "id.mm"
include "nelpr1.mm"
include "neneqd.mm"
include "syl.mm"
include "nelpr2.mm"
include "syl2anc.mm"
include "0ex.mm"
include "fvmpt2.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "iunxdif3.mm"
include "eqcomd.mm"
include "wss.mm"
include "1nn.mm"
include "2nn.mm"
include "pm3.2i.mm"
include "prssi.mm"
include "ax-mp.mm"
include "dfss4.mm"
include "mpbi.mm"
include "iuneq1.mm"
include "fveq2.mm"
include "iunxprg.mm"
include "mp2an.mm"
include "fvmptd.mm"
include "wne.mm"
include "1ne2.mm"
include "necomi.mm"
include "eqnetrd.mm"
include "uneq12d.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "nfv.mm"
include "nnex.mm"
include "cfn.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "elpwi.mm"
include "ovncl.mm"
include "cc0.mm"
include "ovn0.mm"
include "sge0ss.mm"
include "eqsstrd.mm"
include "sge0pr.mm"
include "oveq12d.mm"
include "breq12d.mm"
include "mpbid.mm"

theorem ovnsubadd2lem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vn: setvar n
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume ovnsubadd2lem.x: |- ( ph -> X e. Fin )
  assume ovnsubadd2lem.a: |- ( ph -> A C_ ( RR ^m X ) )
  assume ovnsubadd2lem.b: |- ( ph -> B C_ ( RR ^m X ) )
  assume ovnsubadd2lem.c: |- C = ( n e. NN |-> if ( n = 1 , A , if ( n = 2 , B , (/) ) ) )

  disjoint A n
  disjoint B n
  disjoint C n
  disjoint X n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( ( voln* ` X ) ` ( A u. B ) ) <_ ( ( ( voln* ` X ) ` A ) +e ( ( voln* ` X ) ` B ) ) )

  proof
    wph
    vn
    cn
    vn
    cv
    #
    cC
    cfv
    #
    ciun
    #
    cX
    covoln
    cfv
    #
    cfv
    #
    vn
    cn
    @1
    @3
    cfv
    #
    cmpt
    csumge0
    cfv
    #
    cle
    wbr
    cA
    cB
    cun
    #
    @3
    cfv
    #
    cA
    @3
    cfv
    #
    cB
    @3
    cfv
    #
    cxad
    co
    #
    cle
    wbr
    wph
    cC
    vn
    cX
    ovnsubadd2lem.x
    wph
    vn
    cn
    @0
    c1
    wceq
    #
    cA
    @0
    c2
    wceq
    #
    cB
    c0
    cif
    #
    cif
    #
    cr
    cX
    cmap
    co
    #
    cpw
    #
    cC
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @12
    @15
    @17
    wcel
    #
    wph
    @12
    @20
    @18
    wph
    @12
    wa
    @15
    cA
    @17
    @12
    @15
    cA
    wceq
    wph
    @12
    cA
    @14
    iftrue
    adantl
    #
    wph
    cA
    @17
    wcel
    @12
    wph
    cA
    @16
    cvv
    wph
    cA
    @16
    cvv
    wph
    cr
    cX
    cmap
    ovexd
    #
    ovnsubadd2lem.a
    ssexd
    #
    ovnsubadd2lem.a
    elpwd
    adantr
    eqeltrd
    adantlr
    @19
    @12
    wn
    #
    wa
    @13
    @20
    wph
    @24
    @13
    @20
    @18
    wph
    @24
    wa
    @13
    wa
    @15
    cB
    @17
    @24
    @13
    @15
    cB
    wceq
    #
    wph
    @24
    @13
    wa
    #
    @15
    @14
    cB
    @26
    @12
    cA
    @14
    @24
    @13
    simpl
    iffalsed
    @26
    @13
    cB
    c0
    @24
    @13
    simpr
    iftrued
    eqtrd
    adantll
    wph
    cB
    @17
    wcel
    @24
    @13
    wph
    cB
    @16
    cvv
    wph
    cB
    @16
    cvv
    @22
    ovnsubadd2lem.b
    ssexd
    #
    ovnsubadd2lem.b
    elpwd
    ad2antrr
    eqeltrd
    adantllr
    @24
    @13
    wn
    #
    @20
    @19
    @24
    @28
    wa
    #
    @15
    c0
    @17
    @29
    @15
    @14
    c0
    @29
    @12
    cA
    @14
    @24
    @28
    simpl
    iffalsed
    @29
    @13
    cB
    c0
    @24
    @28
    simpr
    iffalsed
    eqtrd
    #
    c0
    @17
    wcel
    @29
    @16
    0elpw
    a1i
    eqeltrd
    adantll
    pm2.61dan
    pm2.61dan
    ovnsubadd2lem.c
    fmptd
    #
    ovnsubadd
    wph
    @4
    @8
    @6
    @11
    cle
    wph
    @2
    @7
    @3
    wph
    @2
    vn
    cn
    cn
    c1
    c2
    cpr
    #
    cdif
    #
    cdif
    #
    @1
    ciun
    #
    vn
    @32
    @1
    ciun
    #
    @7
    wph
    @35
    @2
    wph
    @1
    c0
    wceq
    #
    vn
    @33
    wral
    @35
    @2
    wceq
    wph
    @37
    vn
    @33
    wph
    @0
    @33
    wcel
    #
    wa
    #
    @1
    @15
    c0
    @39
    @18
    @15
    cvv
    wcel
    #
    @1
    @15
    wceq
    @38
    @18
    wph
    @0
    cn
    @32
    eldifi
    adantl
    @38
    @40
    wph
    @38
    @15
    c0
    cvv
    @38
    @24
    @28
    @15
    c0
    wceq
    #
    @38
    @0
    @32
    wcel
    #
    wn
    #
    @24
    @0
    cn
    @32
    eldifn
    #
    @43
    @0
    c1
    @43
    @0
    c1
    c2
    cvv
    @0
    cvv
    wcel
    @43
    vn
    vex
    a1i
    #
    @43
    id
    #
    nelpr1
    neneqd
    syl
    @38
    @43
    @28
    @44
    @43
    @0
    c2
    @43
    @0
    c1
    c2
    cvv
    @45
    @46
    nelpr2
    neneqd
    syl
    @30
    syl2anc
    #
    c0
    cvv
    wcel
    @38
    0ex
    a1i
    eqeltrd
    adantl
    vn
    cn
    @15
    cvv
    cC
    ovnsubadd2lem.c
    fvmpt2
    syl2anc
    @38
    @41
    wph
    @47
    adantl
    eqtrd
    #
    ralrimiva
    vn
    cn
    @1
    @33
    vn
    @33
    nfcv
    iunxdif3
    syl
    eqcomd
    @35
    @36
    wceq
    #
    wph
    @34
    @32
    wceq
    #
    @49
    @32
    cn
    wss
    #
    @50
    c1
    cn
    wcel
    #
    c2
    cn
    wcel
    #
    wa
    @51
    @52
    @53
    1nn
    2nn
    pm3.2i
    c1
    c2
    cn
    prssi
    ax-mp
    #
    @32
    cn
    dfss4
    mpbi
    vn
    @34
    @32
    @1
    iuneq1
    ax-mp
    a1i
    wph
    @36
    c1
    cC
    cfv
    #
    c2
    cC
    cfv
    #
    cun
    #
    @7
    @7
    @36
    @57
    wceq
    #
    wph
    @52
    @53
    @58
    1nn
    2nn
    vn
    c1
    c2
    @1
    @55
    @56
    cn
    cn
    @0
    c1
    cC
    fveq2
    #
    @0
    c2
    cC
    fveq2
    #
    iunxprg
    mp2an
    a1i
    wph
    @55
    cA
    @56
    cB
    wph
    vn
    c1
    @15
    cA
    cn
    cC
    cvv
    cC
    vn
    cn
    @15
    cmpt
    wceq
    wph
    ovnsubadd2lem.c
    a1i
    #
    @21
    @52
    wph
    1nn
    a1i
    #
    @23
    fvmptd
    #
    wph
    vn
    c2
    @15
    cB
    cn
    cC
    cvv
    @61
    @13
    @25
    wph
    @13
    @15
    @14
    cB
    @13
    @12
    cA
    @14
    @13
    @0
    c1
    @13
    @0
    c2
    c1
    @13
    id
    c2
    c1
    wne
    @13
    c1
    c2
    1ne2
    necomi
    a1i
    eqnetrd
    neneqd
    iffalsed
    @13
    cB
    c0
    iftrue
    eqtrd
    adantl
    @53
    wph
    2nn
    a1i
    #
    @27
    fvmptd
    #
    uneq12d
    wph
    @7
    eqidd
    3eqtrd
    3eqtrd
    fveq2d
    wph
    @6
    vn
    @32
    @5
    cmpt
    csumge0
    cfv
    #
    @55
    @3
    cfv
    #
    @56
    @3
    cfv
    #
    cxad
    co
    @11
    wph
    @66
    @6
    wph
    @32
    cn
    @5
    vn
    cvv
    wph
    vn
    nfv
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    @51
    wph
    @54
    a1i
    #
    wph
    @42
    wa
    #
    @1
    cX
    wph
    cX
    cfn
    wcel
    #
    @42
    ovnsubadd2lem.x
    adantr
    @70
    wph
    @18
    @1
    @16
    wss
    #
    wph
    @42
    simpl
    wph
    @32
    cn
    @0
    @69
    sselda
    @19
    @1
    @17
    wcel
    @72
    wph
    cn
    @17
    @0
    cC
    @31
    ffvelrnda
    @1
    @16
    elpwi
    syl
    syl2anc
    ovncl
    @39
    @5
    c0
    @3
    cfv
    cc0
    @39
    @1
    c0
    @3
    @48
    fveq2d
    @39
    cX
    wph
    @71
    @38
    ovnsubadd2lem.x
    adantr
    ovn0
    eqtrd
    sge0ss
    eqcomd
    wph
    c1
    c2
    @5
    @67
    vn
    @68
    cn
    cn
    @62
    @64
    wph
    @55
    cX
    ovnsubadd2lem.x
    wph
    @55
    cA
    @16
    @63
    ovnsubadd2lem.a
    eqsstrd
    ovncl
    wph
    @56
    cX
    ovnsubadd2lem.x
    wph
    @56
    cB
    @16
    @65
    ovnsubadd2lem.b
    eqsstrd
    ovncl
    @12
    @1
    @55
    @3
    @59
    fveq2d
    @13
    @1
    @56
    @3
    @60
    fveq2d
    c1
    c2
    wne
    wph
    1ne2
    a1i
    sge0pr
    wph
    @67
    @9
    @68
    @10
    cxad
    wph
    @55
    cA
    @3
    @63
    fveq2d
    wph
    @56
    cB
    @3
    @65
    fveq2d
    oveq12d
    3eqtrd
    breq12d
    mpbid
end
