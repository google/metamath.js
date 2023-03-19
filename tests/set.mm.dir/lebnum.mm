include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "crp.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "ccmp.mm"
include "wcel.mm"
include "cxmt.mm"
include "cme.mm"
include "metxmet.mm"
include "syl.mm"
include "mopnuni.mm"
include "eqtr3d.mm"
include "eqid.mm"
include "cmpcov.mm"
include "syl3anc.mm"
include "wa.mm"
include "c1.mm"
include "1rp.mm"
include "inss1.mm"
include "simprl.mm"
include "sseldi.mm"
include "elpwid.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "sseldd.mm"
include "cxr.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "rpxr.mm"
include "mp1i.mm"
include "blssm.mm"
include "sseq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "sylancr.mm"
include "wn.mm"
include "cdif.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "cinf.mm"
include "csu.mm"
include "cioo.mm"
include "ctg.mm"
include "adantr.mm"
include "sstrd.mm"
include "simplrr.mm"
include "eqtrd.mm"
include "inss2.mm"
include "lebnumlem3.mm"
include "wi.mm"
include "ssrexv.mm"
include "ralimdv.mm"
include "reximdv.mm"
include "mpd.mm"
include "pm2.61dan.mm"
include "rexlimddv.mm"

theorem lebnum
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cD: class D
  let cU: class U
  let cJ: class J
  let cX: class X
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vr: setvar r
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cK: class K
  assume lebnum.j: |- J = ( MetOpen ` D )
  assume lebnum.d: |- ( ph -> D e. ( Met ` X ) )
  assume lebnum.c: |- ( ph -> J e. Comp )
  assume lebnum.s: |- ( ph -> U C_ J )
  assume lebnum.u: |- ( ph -> X = U. U )

  disjoint d u
  disjoint d x
  disjoint D d
  disjoint u x
  disjoint D u
  disjoint D x
  disjoint J d
  disjoint J x
  disjoint U d
  disjoint U u
  disjoint U x
  disjoint d ph
  disjoint ph x
  disjoint X d
  disjoint X u
  disjoint X x
  disjoint d k
  disjoint d m
  disjoint d r
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint k m
  disjoint k r
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint D k
  disjoint m r
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint r u
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint J k
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint U k
  disjoint U m
  disjoint U r
  disjoint U w
  disjoint U y
  disjoint U z
  disjoint F r
  disjoint F w
  disjoint F x
  disjoint k ph
  disjoint m ph
  disjoint ph r
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint X k
  disjoint X m
  disjoint X r
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint K x
  assert |- ( ph -> E. d e. RR+ A. x e. X E. u e. U ( x ( ball ` D ) d ) C_ u )

  proof
    wph
    cJ
    cuni
    #
    vw
    cv
    #
    cuni
    #
    wceq
    #
    vx
    cv
    #
    vd
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    vu
    cv
    #
    wss
    #
    vu
    cU
    wrex
    #
    vx
    cX
    wral
    #
    vd
    crp
    wrex
    #
    vw
    cU
    cpw
    #
    cfn
    cin
    #
    wph
    cJ
    ccmp
    wcel
    #
    cU
    cJ
    wss
    #
    @0
    cU
    cuni
    #
    wceq
    @3
    vw
    @14
    wrex
    lebnum.c
    lebnum.s
    wph
    cX
    @0
    @17
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cX
    @0
    wceq
    #
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    @18
    lebnum.d
    cD
    cX
    metxmet
    syl
    #
    cD
    cJ
    cX
    lebnum.j
    mopnuni
    syl
    #
    lebnum.u
    eqtr3d
    cU
    cJ
    @0
    vw
    @0
    eqid
    cmpcov
    syl3anc
    wph
    @1
    @14
    wcel
    #
    @3
    wa
    #
    wa
    #
    cX
    @1
    wcel
    #
    @12
    @25
    @26
    wa
    #
    c1
    crp
    wcel
    #
    @4
    c1
    @6
    co
    #
    @8
    wss
    #
    vu
    cU
    wrex
    #
    vx
    cX
    wral
    #
    @12
    1rp
    @27
    @31
    vx
    cX
    @27
    @4
    cX
    wcel
    #
    wa
    #
    cX
    cU
    wcel
    @29
    cX
    wss
    #
    @31
    @34
    @1
    cU
    cX
    @25
    @1
    cU
    wss
    #
    @26
    @33
    @25
    @1
    cU
    @25
    @14
    @13
    @1
    @13
    cfn
    inss1
    wph
    @23
    @3
    simprl
    #
    sseldi
    elpwid
    #
    ad2antrr
    @25
    @26
    @33
    simplr
    sseldd
    @34
    @18
    @33
    c1
    cxr
    wcel
    #
    @35
    wph
    @18
    @24
    @26
    @33
    @21
    ad3antrrr
    @27
    @33
    simpr
    @28
    @39
    @34
    1rp
    c1
    rpxr
    mp1i
    cD
    @4
    c1
    cX
    blssm
    syl3anc
    @30
    @35
    vu
    cX
    cU
    @8
    cX
    @29
    sseq2
    rspcev
    syl2anc
    ralrimiva
    @11
    @32
    vd
    c1
    crp
    @5
    c1
    wceq
    #
    @10
    @31
    vx
    cX
    @40
    @9
    @30
    vu
    cU
    @40
    @7
    @29
    @8
    @5
    c1
    @4
    @6
    oveq2
    sseq1d
    rexbidv
    ralbidv
    rspcev
    sylancr
    @25
    @26
    wn
    #
    wa
    #
    @9
    vu
    @1
    wrex
    #
    vx
    cX
    wral
    #
    vd
    crp
    wrex
    @12
    @42
    vx
    vy
    vz
    vu
    cD
    @1
    vk
    vy
    cX
    @1
    vz
    cX
    vk
    cv
    cdif
    vy
    cv
    vz
    cv
    cD
    co
    cmpt
    crn
    cxr
    clt
    cinf
    vk
    csu
    cmpt
    #
    cJ
    cioo
    crn
    ctg
    cfv
    #
    cX
    vd
    lebnum.j
    wph
    @20
    @24
    @41
    lebnum.d
    ad2antrr
    wph
    @15
    @24
    @41
    lebnum.c
    ad2antrr
    @42
    @1
    cU
    cJ
    @25
    @36
    @41
    @38
    adantr
    #
    wph
    @16
    @24
    @41
    lebnum.s
    ad2antrr
    sstrd
    @42
    cX
    @0
    @2
    wph
    @19
    @24
    @41
    @22
    ad2antrr
    wph
    @23
    @3
    @41
    simplrr
    eqtrd
    @25
    @1
    cfn
    wcel
    @41
    @25
    @14
    cfn
    @1
    @13
    cfn
    inss2
    @37
    sseldi
    adantr
    @25
    @41
    simpr
    @45
    eqid
    @46
    eqid
    lebnumlem3
    @42
    @44
    @11
    vd
    crp
    @42
    @43
    @10
    vx
    cX
    @42
    @36
    @43
    @10
    wi
    @47
    @9
    vu
    @1
    cU
    ssrexv
    syl
    ralimdv
    reximdv
    mpd
    pm2.61dan
    rexlimddv
end
