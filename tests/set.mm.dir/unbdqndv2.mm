include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "eqid.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "adantr.mm"
include "wf.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wrex.mm"
include "crp.mm"
include "wne.mm"
include "c2.mm"
include "cmul.mm"
include "w3a.mm"
include "wral.mm"
include "wceq.mm"
include "breq1.mm"
include "3anbi3d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "ad2antrr.mm"
include "2rp.mm"
include "simprl.mm"
include "rpmulcld.mm"
include "rspcdva.mm"
include "simprr.mm"
include "rsp.mm"
include "sylc.mm"
include "cif.mm"
include "ad3antrrr.mm"
include "dvbss.mm"
include "simpr.mm"
include "sseldd.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr2r.mm"
include "simpr1l.mm"
include "simpr1r.mm"
include "simpr2l.mm"
include "simpr3.mm"
include "unbdqndv2lem2.mm"
include "simpld.mm"
include "wb.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "fveq2.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "adantl.mm"
include "simprd.mm"
include "rspcedvd.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "unbdqndv1.mm"
include "pm2.01da.mm"

theorem unbdqndv2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cX: class X
  let vb: setvar b
  let vd: setvar d
  let vc: setvar c
  let vw: setvar w
  let vz: setvar z
  assume unbdqndv2.x: |- ( ph -> X C_ RR )
  assume unbdqndv2.f: |- ( ph -> F : X --> CC )
  assume unbdqndv2.1: |- ( ph -> A. b e. RR+ A. d e. RR+ E. x e. X E. y e. X ( ( x <_ A /\ A <_ y ) /\ ( ( y - x ) < d /\ x =/= y ) /\ b <_ ( ( abs ` ( ( F ` y ) - ( F ` x ) ) ) / ( y - x ) ) ) )

  disjoint A b
  disjoint A d
  disjoint A x
  disjoint A y
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint d x
  disjoint d y
  disjoint x y
  disjoint F b
  disjoint F d
  disjoint F x
  disjoint F y
  disjoint X b
  disjoint X d
  disjoint X x
  disjoint X y
  disjoint b ph
  disjoint d ph
  disjoint ph x
  disjoint ph y
  disjoint A c
  disjoint b c
  disjoint c d
  disjoint c x
  disjoint c y
  disjoint A w
  disjoint A z
  disjoint c w
  disjoint c z
  disjoint d w
  disjoint d z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint F c
  disjoint F w
  disjoint F z
  disjoint X c
  disjoint X w
  disjoint X z
  disjoint c ph
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> -. A e. dom ( RR _D F ) )

  proof
    wph
    cA
    cr
    cF
    cdv
    co
    cdm
    #
    wcel
    #
    wph
    @1
    wa
    #
    vw
    vz
    cA
    cr
    cF
    vz
    cX
    cA
    csn
    cdif
    #
    vz
    cv
    #
    cF
    cfv
    cA
    cF
    cfv
    #
    cmin
    co
    @4
    cA
    cmin
    co
    cdiv
    co
    cmpt
    #
    cX
    vc
    vd
    @6
    eqid
    #
    cr
    cc
    wss
    @2
    ax-resscn
    a1i
    #
    wph
    cX
    cr
    wss
    #
    @1
    unbdqndv2.x
    adantr
    #
    wph
    cX
    cc
    cF
    wf
    #
    @1
    unbdqndv2.f
    adantr
    #
    @2
    vw
    cv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    vd
    cv
    #
    clt
    wbr
    #
    vc
    cv
    #
    @13
    @6
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wa
    #
    vw
    @3
    wrex
    #
    vc
    vd
    crp
    crp
    @2
    @18
    crp
    wcel
    #
    @16
    crp
    wcel
    #
    wa
    #
    wa
    #
    vx
    cv
    #
    cA
    cle
    wbr
    #
    cA
    vy
    cv
    #
    cle
    wbr
    #
    wa
    #
    @30
    @28
    cmin
    co
    #
    @16
    clt
    wbr
    #
    @28
    @30
    wne
    #
    wa
    #
    c2
    @18
    cmul
    co
    #
    @30
    cF
    cfv
    @28
    cF
    cfv
    #
    cmin
    co
    cabs
    cfv
    @33
    cdiv
    co
    #
    cle
    wbr
    #
    w3a
    #
    vy
    cX
    wrex
    #
    vx
    cX
    wrex
    #
    @23
    @27
    @43
    vd
    crp
    wral
    #
    @25
    @43
    @27
    @32
    @36
    vb
    cv
    #
    @39
    cle
    wbr
    #
    w3a
    #
    vy
    cX
    wrex
    #
    vx
    cX
    wrex
    #
    vd
    crp
    wral
    #
    @44
    vb
    crp
    @37
    @45
    @37
    wceq
    #
    @49
    @43
    vd
    crp
    @51
    @48
    @42
    vx
    cX
    @51
    @47
    @41
    vy
    cX
    @51
    @46
    @40
    @32
    @36
    @45
    @37
    @39
    cle
    breq1
    3anbi3d
    rexbidv
    rexbidv
    ralbidv
    wph
    @50
    vb
    crp
    wral
    @1
    @26
    unbdqndv2.1
    ad2antrr
    @27
    c2
    @18
    c2
    crp
    wcel
    @27
    2rp
    a1i
    @2
    @24
    @25
    simprl
    #
    rpmulcld
    rspcdva
    @2
    @24
    @25
    simprr
    #
    @43
    vd
    crp
    rsp
    sylc
    @27
    @41
    @23
    vx
    vy
    cX
    cX
    @27
    @28
    cX
    wcel
    #
    @30
    cX
    wcel
    #
    wa
    #
    wa
    #
    @41
    @23
    @57
    @41
    wa
    #
    @22
    @18
    @33
    cmul
    co
    @38
    @5
    cmin
    co
    cabs
    cfv
    cle
    wbr
    @28
    @30
    cif
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @16
    clt
    wbr
    #
    @18
    @59
    @6
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wa
    #
    vw
    @59
    @3
    @58
    @59
    @3
    wcel
    #
    @66
    @58
    vz
    cA
    @18
    @16
    @28
    cF
    @6
    @30
    @59
    cX
    @7
    @59
    eqid
    @2
    @9
    @26
    @56
    @41
    @10
    ad3antrrr
    @2
    @11
    @26
    @56
    @41
    @12
    ad3antrrr
    @57
    cA
    cX
    wcel
    #
    @41
    @27
    @68
    @56
    @2
    @68
    @26
    @2
    @0
    cX
    cA
    @2
    cX
    cr
    cF
    @8
    @12
    @10
    dvbss
    wph
    @1
    simpr
    sseldd
    adantr
    adantr
    adantr
    @27
    @24
    @56
    @41
    @52
    ad2antrr
    @27
    @25
    @56
    @41
    @53
    ad2antrr
    @27
    @54
    @55
    @41
    simplrl
    @27
    @54
    @55
    @41
    simplrr
    @34
    @35
    @32
    @40
    @57
    simpr2r
    @29
    @31
    @36
    @40
    @57
    simpr1l
    @29
    @31
    @36
    @40
    @57
    simpr1r
    @34
    @35
    @32
    @40
    @57
    simpr2l
    @57
    @32
    @36
    @40
    simpr3
    unbdqndv2lem2
    #
    simpld
    @13
    @59
    wceq
    #
    @22
    @66
    wb
    @58
    @70
    @17
    @62
    @21
    @65
    @70
    @15
    @61
    @16
    clt
    @70
    @14
    @60
    cabs
    @13
    @59
    cA
    cmin
    oveq1
    fveq2d
    breq1d
    @70
    @20
    @64
    @18
    cle
    @70
    @19
    @63
    cabs
    @13
    @59
    @6
    fveq2
    fveq2d
    breq2d
    anbi12d
    adantl
    @58
    @67
    @66
    @69
    simprd
    rspcedvd
    ex
    rexlimdvva
    mpd
    ralrimivva
    unbdqndv1
    pm2.01da
end
