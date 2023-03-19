include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cres.mm"
include "csumge0.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "wrex.mm"
include "cr.mm"
include "wcel.mm"
include "wral.mm"
include "cxr.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "sge0sup.mm"
include "eqtr3d.mm"
include "wss.mm"
include "wb.mm"
include "wa.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "adantr.mm"
include "elpwinss.mm"
include "adantl.mm"
include "fssresd.mm"
include "sge0xrcl.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"
include "syl.mm"
include "supxrunb2.mm"
include "mpbird.mm"
include "breq1.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "w3a.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "nf3an.mm"
include "wi.mm"
include "simpl.mm"
include "simpr.mm"
include "breq2d.mm"
include "mpbid.mm"
include "ex.mm"
include "a1d.mm"
include "3adant2.mm"
include "reximdai.mm"
include "mpd.mm"
include "3exp.mm"
include "rexlimdv.mm"

theorem sge0pnffigt
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume sge0pnffigt.x: |- ( ph -> X e. V )
  assume sge0pnffigt.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume sge0pnffigt.pnf: |- ( ph -> ( sum^ ` F ) = +oo )
  assume sge0pnffigt.y: |- ( ph -> Y e. RR )

  disjoint F x
  disjoint X x
  disjoint Y x
  disjoint ph x
  disjoint F y
  disjoint F z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X y
  disjoint X z
  disjoint Y y
  disjoint Y z
  disjoint ph z
  disjoint k x
  assert |- ( ph -> E. x e. ( ~P X i^i Fin ) Y < ( sum^ ` ( F |` x ) ) )

  proof
    wph
    cY
    vz
    cv
    #
    clt
    wbr
    #
    vz
    vx
    cX
    cpw
    cfn
    cin
    #
    cF
    vx
    cv
    #
    cres
    #
    csumge0
    cfv
    #
    cmpt
    #
    crn
    #
    wrex
    #
    cY
    @5
    clt
    wbr
    #
    vx
    @2
    wrex
    #
    wph
    cY
    cr
    wcel
    vy
    cv
    #
    @0
    clt
    wbr
    #
    vz
    @7
    wrex
    #
    vy
    cr
    wral
    #
    @8
    sge0pnffigt.y
    wph
    @14
    @7
    cxr
    clt
    csup
    #
    cpnf
    wceq
    #
    wph
    cF
    csumge0
    cfv
    @15
    cpnf
    wph
    vx
    cF
    cV
    cX
    sge0pnffigt.x
    sge0pnffigt.f
    sge0sup
    sge0pnffigt.pnf
    eqtr3d
    wph
    @7
    cxr
    wss
    #
    @14
    @16
    wb
    wph
    @5
    cxr
    wcel
    #
    vx
    @2
    wral
    @17
    wph
    @18
    vx
    @2
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @4
    cvv
    @3
    @3
    cvv
    wcel
    @20
    vx
    vex
    a1i
    @20
    cX
    cc0
    cpnf
    cicc
    co
    #
    @3
    cF
    wph
    cX
    @21
    cF
    wf
    @19
    sge0pnffigt.f
    adantr
    @19
    @3
    cX
    wss
    wph
    @3
    cX
    cfn
    elpwinss
    adantl
    fssresd
    sge0xrcl
    ralrimiva
    vx
    @2
    @5
    cxr
    @6
    @6
    eqid
    #
    rnmptss
    syl
    vy
    vz
    @7
    supxrunb2
    syl
    mpbird
    @13
    @8
    vy
    cY
    cr
    @11
    cY
    wceq
    @12
    @1
    vz
    @7
    @11
    cY
    @0
    clt
    breq1
    rexbidv
    rspcva
    syl2anc
    wph
    @1
    @10
    vz
    @7
    wph
    @0
    @7
    wcel
    #
    @1
    @10
    wph
    @23
    @1
    w3a
    #
    @0
    @5
    wceq
    #
    vx
    @2
    wrex
    #
    @10
    @23
    wph
    @26
    @1
    @23
    @26
    @0
    cvv
    wcel
    @23
    @26
    wb
    vz
    vex
    vx
    @2
    @5
    @0
    @6
    cvv
    @22
    elrnmpt
    ax-mp
    biimpi
    3ad2ant2
    @24
    @25
    @9
    vx
    @2
    wph
    @23
    @1
    vx
    wph
    vx
    nfv
    vx
    @0
    @7
    vx
    @0
    nfcv
    vx
    @6
    vx
    @2
    @5
    nfmpt1
    nfrn
    nfel
    @1
    vx
    nfv
    nf3an
    wph
    @1
    @19
    @25
    @9
    wi
    #
    wi
    @23
    wph
    @1
    wa
    @27
    @19
    @1
    @27
    wph
    @1
    @25
    @9
    @1
    @25
    wa
    #
    @1
    @9
    @1
    @25
    simpl
    @28
    @0
    @5
    cY
    clt
    @1
    @25
    simpr
    breq2d
    mpbid
    ex
    adantl
    a1d
    3adant2
    reximdai
    mpd
    3exp
    rexlimdv
    mpd
end
