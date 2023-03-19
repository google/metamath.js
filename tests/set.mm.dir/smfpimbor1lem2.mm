include "ccnv.mm"
include "cima.mm"
include "crest.mm"
include "co.mm"
include "cr.mm"
include "cpw.mm"
include "wcel.mm"
include "wa.mm"
include "ctop.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "retop.mm"
include "eqeltri.mm"
include "a1i.mm"
include "smfresal.mm"
include "cv.mm"
include "csalg.mm"
include "adantr.mm"
include "csmblfn.mm"
include "simpr.mm"
include "smfpimbor1lem1.mm"
include "ssd.mm"
include "cuni.mm"
include "wss.mm"
include "wral.mm"
include "wrex.mm"
include "nfcv.mm"
include "crab.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "eluni2f.mm"
include "biimpi.mm"
include "nfuni.mm"
include "nfel.mm"
include "nfv.mm"
include "wi.mm"
include "eleq2i.mm"
include "rabidim1.mm"
include "syl.mm"
include "elpwi.mm"
include "sseldd.mm"
include "ex.mm"
include "rexlimd.mm"
include "mpd.mm"
include "rgen.mm"
include "dfss3.mm"
include "mpbir.mm"
include "wceq.mm"
include "uniretop.mm"
include "eqcomi.mm"
include "unieqi.mm"
include "eqtr2i.mm"
include "eqcomd.mm"
include "unissd.mm"
include "eqsstrd.mm"
include "eqssd.mm"
include "eqtr4d.mm"
include "salgenss.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "sylib.mm"
include "simprd.mm"
include "syl5eqel.mm"

theorem smfpimbor1lem2
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cJ: class J
  let vx: setvar x
  let vk: setvar k
  assume smfpimbor1lem2.s: |- ( ph -> S e. SAlg )
  assume smfpimbor1lem2.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smfpimbor1lem2.a: |- D = dom F
  assume smfpimbor1lem2.j: |- J = ( topGen ` ran (,) )
  assume smfpimbor1lem2.b: |- B = ( SalGen ` J )
  assume smfpimbor1lem2.e: |- ( ph -> E e. B )
  assume smfpimbor1lem2.p: |- P = ( `' F " E )
  assume smfpimbor1lem2.t: |- T = { e e. ~P RR | ( `' F " e ) e. ( S |`t D ) }

  disjoint D e
  disjoint E e
  disjoint F e
  disjoint J e
  disjoint S e
  disjoint e ph
  disjoint D x
  disjoint e x
  disjoint E x
  disjoint F x
  disjoint J x
  disjoint T x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> P e. ( S |`t D ) )

  proof
    wph
    cP
    cF
    ccnv
    #
    cE
    cima
    #
    cS
    cD
    crest
    co
    #
    smfpimbor1lem2.p
    wph
    cE
    cr
    cpw
    #
    wcel
    #
    @1
    @2
    wcel
    #
    wph
    cE
    cT
    wcel
    @4
    @5
    wa
    wph
    cB
    cT
    cE
    wph
    cT
    cB
    ctop
    cJ
    cJ
    ctop
    wcel
    wph
    cJ
    cioo
    crn
    ctg
    cfv
    #
    ctop
    smfpimbor1lem2.j
    retop
    eqeltri
    a1i
    smfpimbor1lem2.b
    wph
    cD
    cS
    cT
    ve
    cF
    smfpimbor1lem2.s
    smfpimbor1lem2.f
    smfpimbor1lem2.a
    smfpimbor1lem2.t
    smfresal
    wph
    vx
    cJ
    cT
    wph
    vx
    cv
    #
    cJ
    wcel
    #
    wa
    cD
    cS
    cT
    ve
    cF
    @7
    cJ
    wph
    cS
    csalg
    wcel
    @8
    smfpimbor1lem2.s
    adantr
    wph
    cF
    cS
    csmblfn
    cfv
    wcel
    @8
    smfpimbor1lem2.f
    adantr
    smfpimbor1lem2.a
    smfpimbor1lem2.j
    wph
    @8
    simpr
    smfpimbor1lem2.t
    smfpimbor1lem1
    ssd
    #
    wph
    cT
    cuni
    #
    cr
    cJ
    cuni
    #
    wph
    @10
    cr
    @10
    cr
    wss
    #
    wph
    @12
    @7
    cr
    wcel
    #
    vx
    @10
    wral
    @13
    vx
    @10
    @7
    @10
    wcel
    #
    @7
    ve
    cv
    #
    wcel
    #
    ve
    cT
    wrex
    #
    @13
    @14
    @17
    ve
    @7
    cT
    ve
    @7
    nfcv
    #
    ve
    cT
    @0
    @15
    cima
    #
    @2
    wcel
    #
    ve
    @3
    crab
    #
    smfpimbor1lem2.t
    @20
    ve
    @3
    nfrab1
    nfcxfr
    #
    eluni2f
    biimpi
    @14
    @16
    @13
    ve
    cT
    ve
    @7
    @10
    @18
    ve
    cT
    @22
    nfuni
    nfel
    @13
    ve
    nfv
    @15
    cT
    wcel
    #
    @16
    @13
    wi
    wi
    @14
    @23
    @16
    @13
    @23
    @16
    wa
    @15
    cr
    @7
    @23
    @15
    cr
    wss
    #
    @16
    @23
    @15
    @3
    wcel
    #
    @24
    @23
    @15
    @21
    wcel
    #
    @25
    @23
    @26
    cT
    @21
    @15
    smfpimbor1lem2.t
    eleq2i
    biimpi
    @20
    ve
    @3
    rabidim1
    syl
    @15
    cr
    elpwi
    syl
    adantr
    @23
    @16
    simpr
    sseldd
    ex
    a1i
    rexlimd
    mpd
    rgen
    vx
    @10
    cr
    dfss3
    mpbir
    a1i
    wph
    cr
    @11
    @10
    wph
    @11
    cr
    @11
    cr
    wceq
    wph
    cr
    @6
    cuni
    @11
    uniretop
    @6
    cJ
    cJ
    @6
    smfpimbor1lem2.j
    eqcomi
    unieqi
    eqtr2i
    a1i
    #
    eqcomd
    wph
    cJ
    cT
    @9
    unissd
    eqsstrd
    eqssd
    @27
    eqtr4d
    salgenss
    smfpimbor1lem2.e
    sseldd
    @20
    @5
    ve
    cE
    @3
    cT
    @15
    cE
    wceq
    @19
    @1
    @2
    @15
    cE
    @0
    imaeq2
    eleq1d
    smfpimbor1lem2.t
    elrab2
    sylib
    simprd
    syl5eqel
end
