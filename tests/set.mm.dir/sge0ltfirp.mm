include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cmin.mm"
include "co.mm"
include "wbr.mm"
include "wrex.mm"
include "csumge0.mm"
include "cres.mm"
include "caddc.mm"
include "sge0rern.mm"
include "fge0iccico.mm"
include "sge0rnre.mm"
include "c0.mm"
include "wne.mm"
include "sge0rnn0.mm"
include "a1i.mm"
include "sge0rnbnd.mm"
include "suprltrp.mm"
include "nfv.mm"
include "wcel.mm"
include "w3a.mm"
include "simp1.mm"
include "wa.mm"
include "wceq.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantr.mm"
include "wi.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfcv.mm"
include "nfsup.mm"
include "nfov.mm"
include "nfbr.mm"
include "simpl.mm"
include "simpr.mm"
include "breqtrd.mm"
include "ex.mm"
include "a1d.mm"
include "reximdai.mm"
include "adantl.mm"
include "mpd.mm"
include "3adant1.mm"
include "sge0supre.mm"
include "oveq1d.mm"
include "eqbrtrd.mm"
include "adantlr.mm"
include "rpred.mm"
include "elinel2.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "rge0ssre.mm"
include "wf.mm"
include "wss.mm"
include "elpwinss.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "fsumrecl.mm"
include "ltsubaddd.mm"
include "mpbid.mm"
include "fssresd.mm"
include "sge0fsum.mm"
include "fvres.mm"
include "sumeq2i.mm"
include "eqtr2d.mm"
include "syl2anc.mm"
include "reximdva.mm"
include "imp.mm"
include "3exp.mm"
include "rexlimd.mm"

theorem sge0ltfirp
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume sge0ltfirp.x: |- ( ph -> X e. V )
  assume sge0ltfirp.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume sge0ltfirp.y: |- ( ph -> Y e. RR+ )
  assume sge0ltfirp.re: |- ( ph -> ( sum^ ` F ) e. RR )

  disjoint F x
  disjoint X x
  disjoint Y x
  disjoint ph x
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint Y w
  disjoint ph w
  disjoint ph y
  disjoint k x
  assert |- ( ph -> E. x e. ( ~P X i^i Fin ) ( sum^ ` F ) < ( ( sum^ ` ( F |` x ) ) + Y ) )

  proof
    wph
    vx
    cX
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    cfv
    #
    vy
    csu
    #
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cY
    cmin
    co
    #
    vw
    cv
    #
    clt
    wbr
    #
    vw
    @7
    wrex
    cF
    csumge0
    cfv
    #
    cF
    @2
    cres
    #
    csumge0
    cfv
    #
    cY
    caddc
    co
    #
    clt
    wbr
    #
    vx
    @1
    wrex
    #
    wph
    vz
    vw
    vw
    @7
    cY
    wph
    vx
    vy
    cF
    cX
    wph
    cF
    cX
    sge0ltfirp.f
    wph
    cF
    cV
    cX
    sge0ltfirp.x
    sge0ltfirp.f
    sge0ltfirp.re
    sge0rern
    fge0iccico
    #
    sge0rnre
    @7
    c0
    wne
    wph
    vx
    vy
    cF
    cX
    sge0rnn0
    a1i
    wph
    vx
    vy
    vz
    vw
    cF
    cV
    cX
    sge0ltfirp.x
    sge0ltfirp.f
    sge0ltfirp.re
    sge0rnbnd
    sge0ltfirp.y
    suprltrp
    wph
    @11
    @17
    vw
    @7
    wph
    vw
    nfv
    @17
    vw
    nfv
    wph
    @10
    @7
    wcel
    #
    @11
    @17
    wph
    @19
    @11
    w3a
    wph
    @9
    @5
    clt
    wbr
    #
    vx
    @1
    wrex
    #
    @17
    wph
    @19
    @11
    simp1
    @19
    @11
    @21
    wph
    @19
    @11
    wa
    @10
    @5
    wceq
    #
    vx
    @1
    wrex
    #
    @21
    @19
    @23
    @11
    @19
    @23
    @10
    cvv
    wcel
    @19
    @23
    wb
    vw
    vex
    vx
    @1
    @5
    @10
    @6
    cvv
    @6
    eqid
    elrnmpt
    ax-mp
    biimpi
    adantr
    @11
    @23
    @21
    wi
    @19
    @11
    @22
    @20
    vx
    @1
    vx
    @9
    @10
    clt
    vx
    @8
    cY
    cmin
    vx
    @7
    cr
    clt
    vx
    @6
    vx
    @1
    @5
    nfmpt1
    nfrn
    vx
    cr
    nfcv
    vx
    clt
    nfcv
    #
    nfsup
    vx
    cmin
    nfcv
    vx
    cY
    nfcv
    nfov
    @24
    vx
    @10
    nfcv
    nfbr
    @11
    @22
    @20
    wi
    @2
    @1
    wcel
    #
    @11
    @22
    @20
    @11
    @22
    wa
    @9
    @10
    @5
    clt
    @11
    @22
    simpl
    @11
    @22
    simpr
    breqtrd
    ex
    a1d
    reximdai
    adantl
    mpd
    3adant1
    wph
    @21
    @17
    wph
    @20
    @16
    vx
    @1
    wph
    @25
    wa
    #
    @20
    @16
    @26
    @20
    wa
    @26
    @12
    cY
    cmin
    co
    #
    @5
    clt
    wbr
    #
    @16
    @26
    @20
    simpl
    wph
    @20
    @28
    @25
    wph
    @20
    wa
    @27
    @9
    @5
    clt
    wph
    @27
    @9
    wceq
    @20
    wph
    @12
    @8
    cY
    cmin
    wph
    vx
    vy
    cF
    cV
    cX
    sge0ltfirp.x
    sge0ltfirp.f
    sge0ltfirp.re
    sge0supre
    oveq1d
    adantr
    wph
    @20
    simpr
    eqbrtrd
    adantlr
    @26
    @28
    wa
    #
    @12
    @5
    cY
    caddc
    co
    #
    @15
    clt
    @29
    @28
    @12
    @30
    clt
    wbr
    #
    @26
    @28
    simpr
    @26
    @28
    @31
    wb
    @28
    @26
    @12
    cY
    @5
    wph
    @12
    cr
    wcel
    @25
    sge0ltfirp.re
    adantr
    wph
    cY
    cr
    wcel
    @25
    wph
    cY
    sge0ltfirp.y
    rpred
    adantr
    @26
    @2
    @4
    vy
    @25
    @2
    cfn
    wcel
    wph
    @2
    @0
    cfn
    elinel2
    adantl
    #
    @26
    @3
    @2
    wcel
    #
    wa
    #
    cc0
    cpnf
    cico
    co
    #
    cr
    @4
    rge0ssre
    @34
    cX
    @35
    @3
    cF
    @26
    cX
    @35
    cF
    wf
    #
    @33
    wph
    @36
    @25
    @18
    adantr
    #
    adantr
    @26
    @2
    cX
    @3
    @25
    @2
    cX
    wss
    wph
    @2
    cX
    cfn
    elpwinss
    adantl
    #
    sselda
    ffvelrnd
    sseldi
    fsumrecl
    ltsubaddd
    adantr
    mpbid
    @26
    @30
    @15
    wceq
    @28
    @26
    @5
    @14
    cY
    caddc
    @26
    @14
    @2
    @3
    @13
    cfv
    #
    vy
    csu
    #
    @5
    @26
    vy
    @13
    @2
    @32
    @26
    cX
    @35
    @2
    cF
    @37
    @38
    fssresd
    sge0fsum
    @40
    @5
    wceq
    @26
    @2
    @39
    @4
    vy
    @3
    @2
    cF
    fvres
    sumeq2i
    a1i
    eqtr2d
    oveq1d
    adantr
    breqtrd
    syl2anc
    ex
    reximdva
    imp
    syl2anc
    3exp
    rexlimd
    mpd
end
