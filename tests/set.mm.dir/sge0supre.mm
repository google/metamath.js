include "csumge0.mm"
include "cfv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "csu.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cr.mm"
include "cpnf.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "adantr.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "simpr.mm"
include "sge0pnfval.mm"
include "wn.mm"
include "sge0repnf.mm"
include "mpbid.mm"
include "pm2.65da.mm"
include "fge0iccico.mm"
include "sge0reval.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "sge0rnre.mm"
include "sge0rnn0.mm"
include "a1i.mm"
include "wb.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "adantl.mm"
include "wi.mm"
include "w3a.mm"
include "simp3.mm"
include "ressxr.mm"
include "sstrd.mm"
include "cvv.mm"
include "id.mm"
include "sumex.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "supxrub.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "3adant3.mm"
include "eqbrtrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "supxrre.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem sge0supre
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cV: class V
  let cX: class X
  let vw: setvar w
  let vz: setvar z
  let vk: setvar k
  assume sge0supre.x: |- ( ph -> X e. V )
  assume sge0supre.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume sge0supre.re: |- ( ph -> ( sum^ ` F ) e. RR )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint ph x
  disjoint ph y
  disjoint F w
  disjoint F z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint X w
  disjoint X z
  disjoint ph w
  disjoint k x
  assert |- ( ph -> ( sum^ ` F ) = sup ( ran ( x e. ( ~P X i^i Fin ) |-> sum_ y e. x ( F ` y ) ) , RR , < ) )

  proof
    wph
    cF
    csumge0
    cfv
    #
    vx
    cX
    cpw
    cfn
    cin
    #
    vx
    cv
    #
    vy
    cv
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
    cxr
    clt
    csup
    #
    @6
    cr
    clt
    csup
    #
    wph
    vx
    vy
    cF
    cV
    cX
    sge0supre.x
    wph
    cF
    cX
    sge0supre.f
    wph
    cpnf
    cF
    crn
    wcel
    #
    @0
    cpnf
    wceq
    #
    wph
    @9
    wa
    cF
    cV
    cX
    wph
    cX
    cV
    wcel
    @9
    sge0supre.x
    adantr
    wph
    cX
    cc0
    cpnf
    cicc
    co
    cF
    wf
    @9
    sge0supre.f
    adantr
    wph
    @9
    simpr
    sge0pnfval
    wph
    @10
    wn
    #
    @9
    wph
    @0
    cr
    wcel
    #
    @11
    sge0supre.re
    wph
    cF
    cV
    cX
    sge0supre.x
    sge0supre.f
    sge0repnf
    mpbid
    adantr
    pm2.65da
    fge0iccico
    #
    sge0reval
    #
    wph
    @6
    cr
    wss
    @6
    c0
    wne
    #
    vw
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    vw
    @6
    wral
    #
    vz
    cr
    wrex
    #
    @7
    @8
    wceq
    wph
    vx
    vy
    cF
    cX
    @13
    sge0rnre
    #
    @15
    wph
    vx
    vy
    cF
    cX
    sge0rnn0
    a1i
    wph
    @12
    @16
    @0
    cle
    wbr
    #
    vw
    @6
    wral
    #
    @20
    sge0supre.re
    wph
    @22
    vw
    @6
    wph
    @16
    @6
    wcel
    #
    wa
    #
    @16
    @4
    wceq
    #
    vx
    @1
    wrex
    #
    @22
    @25
    @24
    @27
    wph
    @24
    simpr
    @24
    @24
    @27
    wb
    wph
    vx
    @1
    @4
    @16
    @5
    @6
    @5
    eqid
    #
    elrnmpt
    adantl
    mpbid
    wph
    @27
    @22
    wi
    @24
    wph
    @26
    @22
    vx
    @1
    wph
    @2
    @1
    wcel
    #
    @26
    @22
    wph
    @29
    @26
    w3a
    @16
    @4
    @0
    cle
    wph
    @29
    @26
    simp3
    wph
    @29
    @4
    @0
    cle
    wbr
    @26
    wph
    @29
    wa
    #
    @4
    @7
    @0
    cle
    @30
    @6
    cxr
    wss
    #
    @4
    @6
    wcel
    #
    @4
    @7
    cle
    wbr
    wph
    @31
    @29
    wph
    @6
    cr
    cxr
    @21
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    sstrd
    adantr
    @29
    @32
    wph
    @29
    @29
    @4
    cvv
    wcel
    #
    @32
    @29
    id
    @33
    @29
    @2
    @3
    vy
    sumex
    a1i
    vx
    @1
    @4
    @5
    cvv
    @28
    elrnmpt1
    syl2anc
    adantl
    @6
    @4
    supxrub
    syl2anc
    wph
    @7
    @0
    wceq
    @29
    wph
    @0
    @7
    @14
    eqcomd
    adantr
    breqtrd
    3adant3
    eqbrtrd
    3exp
    rexlimdv
    adantr
    mpd
    ralrimiva
    @19
    @23
    vz
    @0
    cr
    @17
    @0
    wceq
    @18
    @22
    vw
    @6
    @17
    @0
    @16
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    vz
    vw
    @6
    supxrre
    syl3anc
    eqtrd
end
