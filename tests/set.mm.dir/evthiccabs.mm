include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "wral.mm"
include "wrex.mm"
include "ccom.mm"
include "cc.mm"
include "cr.mm"
include "ccncf.mm"
include "wss.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "sseldi.mm"
include "wcel.mm"
include "abscncf.mm"
include "a1i.mm"
include "cncfco.mm"
include "evthicc.mm"
include "simpld.mm"
include "wa.mm"
include "wceq.mm"
include "wfun.mm"
include "cdm.mm"
include "wf.mm"
include "cncff.mm"
include "ffun.mm"
include "3syl.mm"
include "adantr.mm"
include "simpr.mm"
include "fdm.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "fvco.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "breq12d.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "simprd.mm"
include "jca.mm"

theorem evthiccabs
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cF: class F
  assume evthiccabs.a: |- ( ph -> A e. RR )
  assume evthiccabs.b: |- ( ph -> B e. RR )
  assume evthiccabs.aleb: |- ( ph -> A <_ B )
  assume evthiccabs.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )

  disjoint A w
  disjoint A z
  disjoint w z
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B w
  disjoint B z
  disjoint B x
  disjoint B y
  disjoint F w
  disjoint F z
  disjoint F x
  disjoint F y
  disjoint ph w
  disjoint ph z
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( E. x e. ( A [,] B ) A. y e. ( A [,] B ) ( abs ` ( F ` y ) ) <_ ( abs ` ( F ` x ) ) /\ E. z e. ( A [,] B ) A. w e. ( A [,] B ) ( abs ` ( F ` z ) ) <_ ( abs ` ( F ` w ) ) ) )

  proof
    wph
    vy
    cv
    #
    cF
    cfv
    cabs
    cfv
    #
    vx
    cv
    #
    cF
    cfv
    cabs
    cfv
    #
    cle
    wbr
    #
    vy
    cA
    cB
    cicc
    co
    #
    wral
    #
    vx
    @5
    wrex
    #
    vz
    cv
    #
    cF
    cfv
    cabs
    cfv
    #
    vw
    cv
    #
    cF
    cfv
    cabs
    cfv
    #
    cle
    wbr
    #
    vw
    @5
    wral
    #
    vz
    @5
    wrex
    #
    wph
    @0
    cabs
    cF
    ccom
    #
    cfv
    #
    @2
    @15
    cfv
    #
    cle
    wbr
    #
    vy
    @5
    wral
    #
    vx
    @5
    wrex
    #
    @7
    wph
    @20
    @8
    @15
    cfv
    #
    @10
    @15
    cfv
    #
    cle
    wbr
    #
    vw
    @5
    wral
    #
    vz
    @5
    wrex
    #
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    @15
    evthiccabs.a
    evthiccabs.b
    evthiccabs.aleb
    wph
    @5
    cc
    cr
    cF
    cabs
    wph
    @5
    cr
    ccncf
    co
    #
    @5
    cc
    ccncf
    co
    #
    cF
    cr
    cc
    wss
    cc
    cc
    wss
    @26
    @27
    wss
    ax-resscn
    cc
    ssid
    @5
    cr
    cc
    cncfss
    mp2an
    evthiccabs.f
    sseldi
    cabs
    cc
    cr
    ccncf
    co
    wcel
    wph
    abscncf
    a1i
    cncfco
    evthicc
    #
    simpld
    wph
    @19
    @6
    vx
    @5
    wph
    @2
    @5
    wcel
    #
    wa
    #
    @18
    @4
    vy
    @5
    @30
    @0
    @5
    wcel
    #
    wa
    @16
    @1
    @17
    @3
    cle
    wph
    @31
    @16
    @1
    wceq
    #
    @29
    wph
    @31
    wa
    #
    cF
    wfun
    #
    @0
    cF
    cdm
    #
    wcel
    @32
    wph
    @34
    @31
    wph
    cF
    @26
    wcel
    #
    @5
    cr
    cF
    wf
    #
    @34
    evthiccabs.f
    @5
    cr
    cF
    cncff
    #
    @5
    cr
    cF
    ffun
    3syl
    #
    adantr
    @33
    @0
    @5
    @35
    wph
    @31
    simpr
    wph
    @5
    @35
    wceq
    #
    @31
    wph
    @35
    @5
    wph
    @36
    @37
    @35
    @5
    wceq
    evthiccabs.f
    @38
    @5
    cr
    cF
    fdm
    3syl
    eqcomd
    #
    adantr
    eleqtrd
    @0
    cabs
    cF
    fvco
    syl2anc
    adantlr
    @30
    @17
    @3
    wceq
    #
    @31
    @30
    @34
    @2
    @35
    wcel
    @42
    wph
    @34
    @29
    @39
    adantr
    @30
    @2
    @5
    @35
    wph
    @29
    simpr
    wph
    @40
    @29
    @41
    adantr
    eleqtrd
    @2
    cabs
    cF
    fvco
    syl2anc
    adantr
    breq12d
    ralbidva
    rexbidva
    mpbid
    wph
    @25
    @14
    wph
    @20
    @25
    @28
    simprd
    wph
    @24
    @13
    vz
    @5
    wph
    @8
    @5
    wcel
    #
    wa
    #
    @23
    @12
    vw
    @5
    @44
    @10
    @5
    wcel
    #
    wa
    @21
    @9
    @22
    @11
    cle
    @44
    @21
    @9
    wceq
    #
    @45
    @44
    @34
    @8
    @35
    wcel
    @46
    wph
    @34
    @43
    @39
    adantr
    @44
    @8
    @5
    @35
    wph
    @43
    simpr
    wph
    @40
    @43
    @41
    adantr
    eleqtrd
    @8
    cabs
    cF
    fvco
    syl2anc
    adantr
    wph
    @45
    @22
    @11
    wceq
    #
    @43
    wph
    @45
    wa
    #
    @34
    @10
    @35
    wcel
    @47
    wph
    @34
    @45
    @39
    adantr
    @48
    @10
    @5
    @35
    wph
    @45
    simpr
    wph
    @40
    @45
    @41
    adantr
    eleqtrd
    @10
    cabs
    cF
    fvco
    syl2anc
    adantlr
    breq12d
    ralbidva
    rexbidva
    mpbid
    jca
end
