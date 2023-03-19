include "come.mm"
include "wcel.mm"
include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cuni.mm"
include "cpw.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "cres.mm"
include "csumge0.mm"
include "wi.mm"
include "cmpt.mm"
include "eqid.mm"
include "0e0iccpnf.mm"
include "a1i.mm"
include "fmpti.mm"
include "eqidd.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "feq1i.mm"
include "dmeqi.mm"
include "cr.mm"
include "0re.mm"
include "rgenw.mm"
include "dmmptg.mm"
include "ax-mp.mm"
include "feq2i.mm"
include "bitri.mm"
include "mpbir.mm"
include "unipw.mm"
include "pweqi.mm"
include "eqcomi.mm"
include "unieqi.mm"
include "3eqtri.mm"
include "pm3.2i.mm"
include "0elpw.mm"
include "elexi.mm"
include "fvmpt.mm"
include "leidi.mm"
include "wss.mm"
include "elpwi.mm"
include "adantl.mm"
include "id.mm"
include "eqtr2i.mm"
include "eleqtrd.mm"
include "syl.mm"
include "adantr.mm"
include "sstrd.mm"
include "wb.mm"
include "simpr.mm"
include "elpwg.mm"
include "mpbird.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "sylancl.mm"
include "breq12d.mm"
include "ralrimiva.mm"
include "rgen.mm"
include "sspwuni.mm"
include "sylib.mm"
include "cvv.mm"
include "vuniex.mm"
include "fvmptd.mm"
include "reseq1d.mm"
include "resmpt.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "nfv.mm"
include "sge0z.mm"
include "a1d.mm"
include "pwexg.mm"
include "mptexg.mm"
include "eqeltrd.mm"
include "isome.mm"

theorem 0ome
  let wph: wff ph
  let vx: setvar x
  let cO: class O
  let cV: class V
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume 0ome.1: |- ( ph -> X e. V )
  assume 0ome.2: |- O = ( x e. ~P X |-> 0 )

  disjoint X x
  disjoint O y
  disjoint O z
  disjoint y z
  disjoint X y
  disjoint X z
  disjoint k x
  assert |- ( ph -> O e. OutMeas )

  proof
    wph
    cO
    come
    wcel
    #
    cO
    cdm
    #
    cc0
    cpnf
    cicc
    co
    #
    cO
    wf
    #
    @1
    @1
    cuni
    #
    cpw
    #
    wceq
    #
    wa
    #
    c0
    cO
    cfv
    cc0
    wceq
    #
    wa
    #
    vz
    cv
    #
    cO
    cfv
    #
    vy
    cv
    #
    cO
    cfv
    #
    cle
    wbr
    #
    vz
    @12
    cpw
    #
    wral
    #
    vy
    @5
    wral
    #
    wa
    #
    @12
    com
    cdom
    wbr
    #
    @12
    cuni
    #
    cO
    cfv
    #
    cO
    @12
    cres
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vy
    @1
    cpw
    #
    wral
    #
    wa
    #
    @28
    wph
    @18
    @27
    @9
    @17
    @7
    @8
    @3
    @6
    @3
    cX
    cpw
    #
    @2
    vy
    @29
    cc0
    cmpt
    #
    wf
    #
    vy
    @29
    @2
    cc0
    @30
    @30
    eqid
    cc0
    @2
    wcel
    @12
    @29
    wcel
    #
    0e0iccpnf
    a1i
    fmpti
    @3
    @1
    @2
    @30
    wf
    @31
    @1
    @2
    cO
    @30
    cO
    vx
    @29
    cc0
    cmpt
    @30
    0ome.2
    vx
    vy
    @29
    cc0
    cc0
    vx
    cv
    @12
    wceq
    cc0
    eqidd
    cbvmptv
    eqtri
    #
    feq1i
    @1
    @29
    @2
    @30
    @1
    @30
    cdm
    #
    @29
    cO
    @30
    @33
    dmeqi
    cc0
    cr
    wcel
    #
    vy
    @29
    wral
    @34
    @29
    wceq
    @35
    vy
    @29
    0re
    rgenw
    vy
    @29
    cc0
    cr
    dmmptg
    ax-mp
    eqtri
    #
    feq2i
    bitri
    mpbir
    @1
    @29
    @29
    cuni
    #
    cpw
    #
    @5
    @36
    @38
    @29
    @37
    cX
    cX
    unipw
    pweqi
    eqcomi
    #
    @37
    @4
    @29
    @1
    @1
    @29
    @36
    eqcomi
    unieqi
    pweqi
    #
    3eqtri
    pm3.2i
    c0
    @29
    wcel
    @8
    cX
    0elpw
    vy
    c0
    cc0
    cc0
    @29
    cO
    @12
    c0
    wceq
    cc0
    eqidd
    @33
    cc0
    cr
    0re
    elexi
    fvmpt
    ax-mp
    pm3.2i
    @16
    vy
    @5
    @12
    @5
    wcel
    #
    @14
    vz
    @15
    @41
    @10
    @15
    wcel
    #
    wa
    #
    @14
    cc0
    cc0
    cle
    wbr
    #
    @44
    @43
    cc0
    0re
    leidi
    #
    a1i
    @43
    @11
    cc0
    @13
    cc0
    cle
    @43
    @10
    @29
    wcel
    #
    @35
    @11
    cc0
    wceq
    @43
    @46
    @10
    cX
    wss
    #
    @43
    @10
    @12
    cX
    @42
    @10
    @12
    wss
    @41
    @10
    @12
    elpwi
    adantl
    @41
    @12
    cX
    wss
    #
    @42
    @41
    @32
    @48
    @41
    @12
    @5
    @29
    @41
    id
    @5
    @29
    wceq
    @41
    @29
    @38
    @5
    @39
    @40
    eqtr2i
    a1i
    eleqtrd
    #
    @12
    cX
    elpwi
    syl
    adantr
    sstrd
    @43
    @42
    @46
    @47
    wb
    @41
    @42
    simpr
    @10
    cX
    @15
    elpwg
    syl
    mpbird
    @35
    @43
    0re
    a1i
    vz
    @29
    cc0
    cr
    cO
    cO
    @30
    vz
    @29
    cc0
    cmpt
    #
    @33
    vy
    vz
    @29
    cc0
    cc0
    @12
    @10
    wceq
    cc0
    eqidd
    cbvmptv
    eqtri
    #
    fvmpt2
    syl2anc
    @41
    @13
    cc0
    wceq
    #
    @42
    @41
    @32
    @35
    @52
    @49
    0re
    vy
    @29
    cc0
    cr
    cO
    @33
    fvmpt2
    sylancl
    adantr
    breq12d
    mpbird
    ralrimiva
    rgen
    pm3.2i
    @25
    vy
    @26
    @12
    @26
    wcel
    #
    @24
    @19
    @53
    @24
    @44
    @44
    @53
    @45
    a1i
    @53
    @21
    cc0
    @23
    cc0
    cle
    @53
    vz
    @20
    cc0
    cc0
    @29
    cO
    cr
    cO
    @50
    wceq
    @53
    @51
    a1i
    #
    @53
    @10
    @20
    wceq
    wa
    cc0
    eqidd
    @53
    @20
    @29
    wcel
    #
    @20
    cX
    wss
    #
    @53
    @12
    @29
    wss
    #
    @56
    @53
    @12
    @29
    cpw
    #
    wcel
    @57
    @53
    @12
    @26
    @58
    @53
    id
    #
    @26
    @58
    wceq
    @53
    @1
    @29
    @36
    pweqi
    a1i
    eleqtrd
    @12
    @29
    elpwi
    syl
    #
    @12
    cX
    sspwuni
    sylib
    @53
    @20
    cvv
    wcel
    #
    @55
    @56
    wb
    @61
    @53
    vy
    vuniex
    a1i
    @20
    cX
    cvv
    elpwg
    syl
    mpbird
    @35
    @53
    0re
    a1i
    fvmptd
    @53
    @23
    vz
    @12
    cc0
    cmpt
    #
    csumge0
    cfv
    cc0
    @53
    @22
    @62
    csumge0
    @53
    @22
    @50
    @12
    cres
    #
    @62
    @53
    cO
    @50
    @12
    @54
    reseq1d
    @53
    @57
    @63
    @62
    wceq
    @60
    vz
    @29
    @12
    cc0
    resmpt
    syl
    eqtrd
    fveq2d
    @53
    @12
    vz
    @26
    @53
    vz
    nfv
    @59
    sge0z
    eqtrd
    breq12d
    mpbird
    a1d
    rgen
    pm3.2i
    a1i
    wph
    cO
    cvv
    wcel
    @0
    @28
    wb
    wph
    cO
    @30
    cvv
    cO
    @30
    wceq
    wph
    @33
    a1i
    wph
    @29
    cvv
    wcel
    #
    @30
    cvv
    wcel
    wph
    cX
    cV
    wcel
    @64
    0ome.1
    cX
    cV
    pwexg
    syl
    vy
    @29
    cc0
    cvv
    mptexg
    syl
    eqeltrd
    vy
    vz
    cO
    cvv
    isome
    syl
    mpbird
end
