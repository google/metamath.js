include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "csalg.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "cuni.mm"
include "cres.mm"
include "csumge0.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cmea.mm"
include "simpr.mm"
include "wss.mm"
include "adantr.mm"
include "elpwid.mm"
include "fssres.mm"
include "syl2anc.mm"
include "sge0cl.mm"
include "fmptd.mm"
include "dmmptd.mm"
include "feq2d.mm"
include "mpbird.mm"
include "pwsal.mm"
include "syl.mm"
include "eqeltrd.mm"
include "jca.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "reseq2.mm"
include "fveq2d.mm"
include "adantl.mm"
include "0elpw.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "res0.mm"
include "fveq2i.mm"
include "sge00.mm"
include "eqtri.mm"
include "eqtrd.mm"
include "simpl.mm"
include "pweqd.mm"
include "eleqtrd.mm"
include "elpwi.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "id.mm"
include "cbvdisjv.mm"
include "biimpi.mm"
include "psmeasurelem.mm"
include "adantrl.mm"
include "ex.mm"
include "ralrimiva.mm"
include "jca31.mm"
include "ismea.mm"
include "sylibr.mm"

theorem psmeasure
  let wph: wff ph
  let vx: setvar x
  let cH: class H
  let cM: class M
  let cV: class V
  let cX: class X
  let vz: setvar z
  let vy: setvar y
  let vw: setvar w
  let vk: setvar k
  assume psmeasure.x: |- ( ph -> X e. V )
  assume psmeasure.h: |- ( ph -> H : X --> ( 0 [,] +oo ) )
  assume psmeasure.m: |- M = ( x e. ~P X |-> ( sum^ ` ( H |` x ) ) )

  disjoint H x
  disjoint X x
  disjoint ph x
  disjoint H z
  disjoint x z
  disjoint M y
  disjoint M z
  disjoint y z
  disjoint X z
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint k x
  assert |- ( ph -> M e. Meas )

  proof
    wph
    cM
    cdm
    #
    cc0
    cpnf
    cicc
    co
    #
    cM
    wf
    #
    @0
    csalg
    wcel
    #
    wa
    #
    c0
    cM
    cfv
    #
    cc0
    wceq
    #
    wa
    vy
    cv
    #
    com
    cdom
    wbr
    #
    vw
    @7
    vw
    cv
    #
    wdisj
    #
    wa
    #
    @7
    cuni
    cM
    cfv
    cM
    @7
    cres
    csumge0
    cfv
    wceq
    #
    wi
    #
    vy
    @0
    cpw
    #
    wral
    #
    wa
    cM
    cmea
    wcel
    wph
    @4
    @6
    @15
    wph
    @2
    @3
    wph
    @2
    cX
    cpw
    #
    @1
    cM
    wf
    #
    wph
    vx
    @16
    cH
    vx
    cv
    #
    cres
    #
    csumge0
    cfv
    #
    @1
    cM
    wph
    @18
    @16
    wcel
    #
    wa
    #
    @19
    @16
    @18
    wph
    @21
    simpr
    #
    @22
    cX
    @1
    cH
    wf
    #
    @18
    cX
    wss
    @18
    @1
    @19
    wf
    wph
    @24
    @21
    psmeasure.h
    adantr
    @22
    @18
    cX
    @23
    elpwid
    cX
    @1
    @18
    cH
    fssres
    syl2anc
    sge0cl
    #
    psmeasure.m
    fmptd
    #
    wph
    @0
    @16
    @1
    cM
    wph
    vx
    cM
    @16
    @20
    @1
    psmeasure.m
    @25
    dmmptd
    #
    feq2d
    mpbird
    wph
    @0
    @16
    csalg
    @27
    wph
    cX
    cV
    wcel
    #
    @16
    csalg
    wcel
    psmeasure.x
    cV
    cX
    pwsal
    syl
    eqeltrd
    jca
    wph
    @5
    cH
    c0
    cres
    #
    csumge0
    cfv
    #
    cc0
    wph
    vx
    c0
    @20
    @30
    @16
    cM
    cvv
    cM
    vx
    @16
    @20
    cmpt
    wceq
    wph
    psmeasure.m
    a1i
    @18
    c0
    wceq
    #
    @20
    @30
    wceq
    wph
    @31
    @19
    @29
    csumge0
    @18
    c0
    cH
    reseq2
    fveq2d
    adantl
    c0
    @16
    wcel
    wph
    cX
    0elpw
    a1i
    wph
    @29
    csumge0
    fvexd
    fvmptd
    @30
    cc0
    wceq
    wph
    @30
    c0
    csumge0
    cfv
    cc0
    @29
    c0
    csumge0
    cH
    res0
    fveq2i
    sge00
    eqtri
    a1i
    eqtrd
    wph
    @13
    vy
    @14
    wph
    @7
    @14
    wcel
    #
    wa
    #
    wph
    @7
    @16
    wss
    #
    @13
    wph
    @32
    simpl
    @33
    @7
    @16
    cpw
    #
    wcel
    @34
    @33
    @7
    @14
    @35
    wph
    @32
    simpr
    wph
    @14
    @35
    wceq
    @32
    wph
    @0
    @16
    @27
    pweqd
    adantr
    eleqtrd
    @7
    @16
    elpwi
    syl
    wph
    @34
    wa
    #
    @11
    @12
    @36
    @10
    @12
    @8
    @36
    @10
    wa
    vx
    vz
    cH
    cM
    cV
    cX
    @7
    wph
    @28
    @34
    @10
    psmeasure.x
    ad2antrr
    wph
    @24
    @34
    @10
    psmeasure.h
    ad2antrr
    psmeasure.m
    wph
    @17
    @34
    @10
    @26
    ad2antrr
    wph
    @34
    @10
    simplr
    @10
    vz
    @7
    vz
    cv
    #
    wdisj
    #
    @36
    @10
    @38
    vw
    vz
    @7
    @9
    @37
    @9
    @37
    wceq
    id
    cbvdisjv
    biimpi
    adantl
    psmeasurelem
    adantrl
    ex
    syl2anc
    ralrimiva
    jca31
    vy
    vw
    cM
    ismea
    sylibr
end
