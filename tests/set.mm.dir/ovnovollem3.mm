include "csn.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "cmap.mm"
include "co.mm"
include "covoln.mm"
include "cfv.mm"
include "covol.mm"
include "wcel.mm"
include "wne.mm"
include "snnzg.mm"
include "syl.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "cfn.mm"
include "snfi.mm"
include "a1i.mm"
include "cr.mm"
include "cvv.mm"
include "wss.mm"
include "reex.mm"
include "mapss.mm"
include "syl2anc.mm"
include "ovnval2.mm"
include "ovolval5.mm"
include "cico.mm"
include "cv.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "cvol.mm"
include "csumge0.mm"
include "wa.mm"
include "cxp.mm"
include "cn.mm"
include "wrex.mm"
include "crab.mm"
include "cixp.mm"
include "ciun.mm"
include "cprod.mm"
include "cmpt.mm"
include "cop.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "fveq2.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "cbvmptv.mm"
include "simprl.mm"
include "ssexd.mm"
include "adantr.mm"
include "simprr.mm"
include "ovnovollem1.mm"
include "3impa.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3l.mm"
include "coeq2d.mm"
include "fveq1d.mm"
include "ixpeq2dv.mm"
include "cbvixpv.mm"
include "eqtrd.mm"
include "cbviunv.mm"
include "sseq2i.mm"
include "biimpi.mm"
include "simp3r.mm"
include "fveq2d.mm"
include "prodeq2ad.mm"
include "cbvprodv.mm"
include "fveq2i.mm"
include "eqeq2i.mm"
include "ovnovollem2.mm"
include "impbid.mm"
include "rabbidv.mm"
include "3eqtr4d.mm"
include "infeq1d.mm"

theorem ovnovollem3
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vl: setvar l
  let vm: setvar m
  let vx: setvar x
  assume ovnovollem3.a: |- ( ph -> A e. V )
  assume ovnovollem3.b: |- ( ph -> B C_ RR )
  assume ovnovollem3.m: |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m { A } ) ^m NN ) ( ( B ^m { A } ) C_ U_ j e. NN X_ k e. { A } ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. { A } ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) }
  assume ovnovollem3.n: |- N = { z e. RR* | E. f e. ( ( RR X. RR ) ^m NN ) ( B C_ U. ran ( [,) o. f ) /\ z = ( sum^ ` ( ( vol o. [,) ) o. f ) ) ) }

  disjoint A f
  disjoint A i
  disjoint A j
  disjoint A k
  disjoint A z
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f z
  disjoint i j
  disjoint i k
  disjoint i z
  disjoint j k
  disjoint j z
  disjoint k z
  disjoint B f
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B z
  disjoint N z
  disjoint V k
  disjoint f ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint ph z
  disjoint A n
  disjoint f n
  disjoint i n
  disjoint j n
  disjoint k n
  disjoint n z
  disjoint A l
  disjoint i l
  disjoint j l
  disjoint k l
  disjoint l n
  disjoint l z
  disjoint A m
  disjoint f m
  disjoint i m
  disjoint m n
  disjoint B n
  disjoint B l
  disjoint V l
  disjoint n ph
  disjoint l m
  disjoint l ph
  disjoint k x
  assert |- ( ph -> ( ( voln* ` { A } ) ` ( B ^m { A } ) ) = ( vol* ` B ) )

  proof
    wph
    cA
    csn
    #
    c0
    wceq
    #
    cc0
    cM
    cxr
    clt
    cinf
    #
    cif
    @2
    cB
    @0
    cmap
    co
    #
    @0
    covoln
    cfv
    cfv
    cB
    covol
    cfv
    #
    wph
    @1
    cc0
    @2
    wph
    @0
    c0
    wph
    cA
    cV
    wcel
    #
    @0
    c0
    wne
    ovnovollem3.a
    cA
    cV
    snnzg
    syl
    neneqd
    iffalsed
    wph
    vz
    @3
    vi
    vj
    vk
    cM
    @0
    @0
    cfn
    wcel
    wph
    cA
    snfi
    a1i
    wph
    cr
    cvv
    wcel
    #
    cB
    cr
    wss
    @3
    cr
    @0
    cmap
    co
    wss
    @6
    wph
    reex
    a1i
    #
    ovnovollem3.b
    cB
    cr
    @0
    cvv
    mapss
    syl2anc
    ovnovollem3.m
    ovnval2
    wph
    @4
    cN
    cxr
    clt
    cinf
    @2
    wph
    vz
    cB
    vf
    cN
    ovnovollem3.b
    ovnovollem3.n
    ovolval5
    wph
    cxr
    cN
    cM
    clt
    wph
    cB
    cico
    vf
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    vz
    cv
    #
    cvol
    cico
    ccom
    @8
    ccom
    csumge0
    cfv
    wceq
    #
    wa
    #
    vf
    cr
    cr
    cxp
    #
    cn
    cmap
    co
    #
    wrex
    #
    vz
    cxr
    crab
    #
    @3
    vj
    cn
    vk
    @0
    vk
    cv
    #
    cico
    vj
    cv
    #
    vi
    cv
    #
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    @10
    vj
    cn
    @0
    @22
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vi
    @13
    @0
    cmap
    co
    cn
    cmap
    co
    #
    wrex
    #
    vz
    cxr
    crab
    #
    cN
    cM
    wph
    @15
    @33
    vz
    cxr
    wph
    @15
    @33
    wph
    @12
    @33
    vf
    @14
    wph
    @8
    @14
    wcel
    #
    @12
    @33
    wph
    @35
    @12
    @33
    wph
    @35
    wa
    #
    @12
    wa
    cA
    cB
    vi
    vj
    vk
    @8
    vn
    cn
    cA
    vn
    cv
    #
    @8
    cfv
    #
    cop
    #
    csn
    #
    cmpt
    cV
    cvv
    @10
    wph
    @5
    @35
    @12
    ovnovollem3.a
    ad2antrr
    wph
    @35
    @12
    simplr
    vn
    vj
    cn
    @40
    cA
    @18
    @8
    cfv
    #
    cop
    #
    csn
    @37
    @18
    wceq
    #
    @39
    @42
    @43
    @38
    @41
    cA
    @37
    @18
    @8
    fveq2
    opeq2d
    sneqd
    cbvmptv
    @36
    @9
    @11
    simprl
    @36
    cB
    cvv
    wcel
    #
    @12
    wph
    @44
    @35
    wph
    cB
    cr
    cvv
    @7
    ovnovollem3.b
    ssexd
    #
    adantr
    adantr
    @36
    @9
    @11
    simprr
    ovnovollem1
    3impa
    3exp
    rexlimdv
    wph
    @31
    @15
    vi
    @32
    wph
    @19
    @32
    wcel
    #
    @31
    @15
    wph
    @46
    @31
    w3a
    #
    cA
    cB
    vf
    vn
    vl
    vm
    cn
    cA
    vm
    cv
    #
    @19
    cfv
    #
    cfv
    #
    cmpt
    @19
    cV
    cvv
    @10
    wph
    @46
    @5
    @31
    ovnovollem3.a
    3ad2ant1
    wph
    @46
    @44
    @31
    @45
    3ad2ant1
    wph
    @46
    @31
    simp2
    @47
    @25
    @3
    vn
    cn
    vl
    @0
    vl
    cv
    #
    cico
    @37
    @19
    cfv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    ciun
    #
    wss
    #
    wph
    @46
    @25
    @30
    simp3l
    @25
    @57
    @24
    @56
    @3
    vj
    vn
    cn
    @23
    @55
    @18
    @37
    wceq
    #
    @23
    vk
    @0
    @17
    @53
    cfv
    #
    cixp
    #
    @55
    @58
    vk
    @0
    @22
    @59
    @58
    @17
    @21
    @53
    @58
    @20
    @52
    cico
    @18
    @37
    @19
    fveq2
    coeq2d
    fveq1d
    #
    ixpeq2dv
    @60
    @55
    wceq
    @58
    vk
    vl
    @0
    @59
    @54
    @17
    @51
    @53
    fveq2
    #
    cbvixpv
    a1i
    eqtrd
    cbviunv
    sseq2i
    biimpi
    syl
    @47
    @30
    @10
    vn
    cn
    @0
    @54
    cvol
    cfv
    #
    vl
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wph
    @46
    @25
    @30
    simp3r
    @30
    @67
    @29
    @66
    @10
    @28
    @65
    csumge0
    vj
    vn
    cn
    @27
    @64
    @58
    @27
    @0
    @59
    cvol
    cfv
    #
    vk
    cprod
    #
    @64
    @58
    @0
    @26
    @68
    vk
    @58
    @22
    @59
    cvol
    @61
    fveq2d
    prodeq2ad
    @69
    @64
    wceq
    @58
    @0
    @68
    @63
    vk
    vl
    @17
    @51
    wceq
    @59
    @54
    cvol
    @62
    fveq2d
    cbvprodv
    a1i
    eqtrd
    cbvmptv
    fveq2i
    eqeq2i
    biimpi
    syl
    vm
    vn
    cn
    @50
    cA
    @52
    cfv
    @48
    @37
    wceq
    cA
    @49
    @52
    @48
    @37
    @19
    fveq2
    fveq1d
    cbvmptv
    ovnovollem2
    3exp
    rexlimdv
    impbid
    rabbidv
    cN
    @16
    wceq
    wph
    ovnovollem3.n
    a1i
    cM
    @34
    wceq
    wph
    ovnovollem3.m
    a1i
    3eqtr4d
    infeq1d
    eqtrd
    3eqtr4d
end
