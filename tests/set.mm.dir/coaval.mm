include "carw.mm"
include "cfv.mm"
include "cv.mm"
include "ccoda.mm"
include "cdoma.mm"
include "wceq.mm"
include "crab.mm"
include "c2nd.mm"
include "cop.mm"
include "co.mm"
include "cotp.mm"
include "cmpt2.mm"
include "eqid.mm"
include "coafval.mm"
include "cvv.mm"
include "homarw.mm"
include "sseldi.mm"
include "wa.mm"
include "wcel.mm"
include "adantr.mm"
include "homacd.mm"
include "syl.mm"
include "simpr.mm"
include "fveq2d.mm"
include "homadm.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "otex.mm"
include "a1i.mm"
include "simprr.mm"
include "adantrr.mm"
include "opeq12d.mm"
include "oveq12d.mm"
include "simprl.mm"
include "oveq123d.mm"
include "oteq123d.mm"
include "ovmpt2dv2.mm"
include "mpi.mm"

theorem coaval
  let wph: wff ph
  let cC: class C
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  assume homdmcoa.o: |- .x. = ( compA ` C )
  assume homdmcoa.h: |- H = ( HomA ` C )
  assume homdmcoa.f: |- ( ph -> F e. ( X H Y ) )
  assume homdmcoa.g: |- ( ph -> G e. ( Y H Z ) )
  assume coaval.x: |- .xb = ( comp ` C )


  assert |- ( ph -> ( G .x. F ) = <. X , Z , ( ( 2nd ` G ) ( <. X , Y >. .xb Z ) ( 2nd ` F ) ) >. )

  proof
    wph
    c.x
    vg
    vf
    cC
    carw
    cfv
    #
    vh
    cv
    #
    ccoda
    cfv
    #
    vg
    cv
    #
    cdoma
    cfv
    #
    wceq
    #
    vh
    @0
    crab
    #
    vf
    cv
    #
    cdoma
    cfv
    #
    @3
    ccoda
    cfv
    #
    @3
    c2nd
    cfv
    #
    @7
    c2nd
    cfv
    #
    @8
    @4
    cop
    #
    @9
    c.xb
    co
    #
    co
    #
    cotp
    #
    cmpt2
    wceq
    cG
    cF
    c.x
    co
    cX
    cZ
    cG
    c2nd
    cfv
    #
    cF
    c2nd
    cfv
    #
    cX
    cY
    cop
    #
    cZ
    c.xb
    co
    #
    co
    #
    cotp
    #
    wceq
    @0
    cC
    c.xb
    c.x
    vf
    vg
    vh
    homdmcoa.o
    @0
    eqid
    #
    coaval.x
    coafval
    wph
    vg
    vf
    cG
    cF
    @0
    @6
    @15
    @21
    c.x
    cvv
    wph
    cY
    cZ
    cH
    co
    #
    @0
    cG
    @0
    cC
    cH
    cY
    cZ
    @22
    homdmcoa.h
    homarw
    homdmcoa.g
    sseldi
    wph
    @3
    cG
    wceq
    #
    wa
    #
    cF
    @0
    wcel
    cF
    ccoda
    cfv
    #
    @4
    wceq
    #
    cF
    @6
    wcel
    @25
    cX
    cY
    cH
    co
    #
    @0
    cF
    @0
    cC
    cH
    cX
    cY
    @22
    homdmcoa.h
    homarw
    wph
    cF
    @28
    wcel
    #
    @24
    homdmcoa.f
    adantr
    #
    sseldi
    @25
    @26
    cY
    @4
    @25
    @29
    @26
    cY
    wceq
    @30
    cC
    cF
    cH
    cX
    cY
    homdmcoa.h
    homacd
    syl
    @25
    @4
    cG
    cdoma
    cfv
    #
    cY
    @25
    @3
    cG
    cdoma
    wph
    @24
    simpr
    #
    fveq2d
    @25
    cG
    @23
    wcel
    #
    @31
    cY
    wceq
    wph
    @33
    @24
    homdmcoa.g
    adantr
    #
    cC
    cG
    cH
    cY
    cZ
    homdmcoa.h
    homadm
    syl
    eqtrd
    #
    eqtr4d
    @5
    @27
    vh
    cF
    @0
    @1
    cF
    wceq
    @2
    @26
    @4
    @1
    cF
    ccoda
    fveq2
    eqeq1d
    elrab
    sylanbrc
    @15
    cvv
    wcel
    wph
    @24
    @7
    cF
    wceq
    #
    wa
    wa
    #
    @8
    @9
    @14
    otex
    a1i
    @37
    @8
    cX
    @9
    cZ
    @14
    @20
    @37
    @8
    cF
    cdoma
    cfv
    #
    cX
    @37
    @7
    cF
    cdoma
    wph
    @24
    @36
    simprr
    #
    fveq2d
    wph
    @24
    @38
    cX
    wceq
    #
    @36
    @25
    @29
    @40
    @30
    cC
    cF
    cH
    cX
    cY
    homdmcoa.h
    homadm
    syl
    adantrr
    eqtrd
    #
    wph
    @24
    @9
    cZ
    wceq
    @36
    @25
    @9
    cG
    ccoda
    cfv
    #
    cZ
    @25
    @3
    cG
    ccoda
    @32
    fveq2d
    @25
    @33
    @42
    cZ
    wceq
    @34
    cC
    cG
    cH
    cY
    cZ
    homdmcoa.h
    homacd
    syl
    eqtrd
    adantrr
    #
    @37
    @10
    @16
    @11
    @17
    @13
    @19
    @37
    @12
    @18
    @9
    cZ
    c.xb
    @37
    @8
    cX
    @4
    cY
    @41
    wph
    @24
    @4
    cY
    wceq
    @36
    @35
    adantrr
    opeq12d
    @43
    oveq12d
    @37
    @3
    cG
    c2nd
    wph
    @24
    @36
    simprl
    fveq2d
    @37
    @7
    cF
    c2nd
    @39
    fveq2d
    oveq123d
    oteq123d
    ovmpt2dv2
    mpi
end
