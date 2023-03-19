include "cmbfm.mm"
include "co.mm"
include "wcel.mm"
include "cuni.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "ccn.mm"
include "eqid.mm"
include "cnf.mm"
include "syl.mm"
include "csigagen.mm"
include "cfv.mm"
include "unieqd.mm"
include "ctop.mm"
include "wceq.mm"
include "cntop1.mm"
include "unisg.mm"
include "3syl.mm"
include "eqtrd.mm"
include "cntop2.mm"
include "feq23d.mm"
include "mpbird.mm"
include "wa.mm"
include "wss.mm"
include "sssigagen.mm"
include "sseqtr4d.mm"
include "adantr.mm"
include "cnima.mm"
include "sylan.mm"
include "sseldd.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "elex.mm"
include "csiga.mm"
include "crn.mm"
include "sigagensiga.mm"
include "eqeltrd.mm"
include "elrnsiga.mm"
include "imambfm.mm"
include "mpbir2and.mm"

theorem cnmbfm
  let wph: wff ph
  let cS: class S
  let cT: class T
  let cF: class F
  let cJ: class J
  let cK: class K
  let va: setvar a
  assume cnmbfm.1: |- ( ph -> F e. ( J Cn K ) )
  assume cnmbfm.2: |- ( ph -> S = ( sigaGen ` J ) )
  assume cnmbfm.3: |- ( ph -> T = ( sigaGen ` K ) )


  assert |- ( ph -> F e. ( S MblFnM T ) )

  proof
    wph
    cF
    cS
    cT
    cmbfm
    co
    wcel
    cS
    cuni
    #
    cT
    cuni
    #
    cF
    wf
    #
    cF
    ccnv
    va
    cv
    #
    cima
    #
    cS
    wcel
    #
    va
    cK
    wral
    wph
    @2
    cJ
    cuni
    #
    cK
    cuni
    #
    cF
    wf
    #
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @8
    cnmbfm.1
    cF
    cJ
    cK
    @6
    @7
    @6
    eqid
    @7
    eqid
    cnf
    syl
    wph
    @0
    @1
    @6
    @7
    cF
    wph
    @0
    cJ
    csigagen
    cfv
    #
    cuni
    #
    @6
    wph
    cS
    @10
    cnmbfm.2
    unieqd
    wph
    @9
    cJ
    ctop
    wcel
    #
    @11
    @6
    wceq
    cnmbfm.1
    cF
    cJ
    cK
    cntop1
    #
    cJ
    ctop
    unisg
    3syl
    eqtrd
    wph
    @1
    cK
    csigagen
    cfv
    #
    cuni
    #
    @7
    wph
    cT
    @14
    cnmbfm.3
    unieqd
    wph
    @9
    cK
    ctop
    wcel
    #
    @15
    @7
    wceq
    cnmbfm.1
    cF
    cJ
    cK
    cntop2
    #
    cK
    ctop
    unisg
    3syl
    eqtrd
    feq23d
    mpbird
    wph
    @5
    va
    cK
    wph
    @3
    cK
    wcel
    #
    wa
    cJ
    cS
    @4
    wph
    cJ
    cS
    wss
    @18
    wph
    cJ
    @10
    cS
    wph
    @9
    @12
    cJ
    @10
    wss
    cnmbfm.1
    @13
    cJ
    ctop
    sssigagen
    3syl
    cnmbfm.2
    sseqtr4d
    adantr
    wph
    @9
    @18
    @4
    cJ
    wcel
    cnmbfm.1
    @3
    cF
    cJ
    cK
    cnima
    sylan
    sseldd
    ralrimiva
    wph
    cS
    cT
    cF
    cK
    va
    wph
    @9
    @16
    cK
    cvv
    wcel
    cnmbfm.1
    @17
    cK
    ctop
    elex
    3syl
    wph
    cS
    @6
    csiga
    cfv
    #
    wcel
    cS
    csiga
    crn
    cuni
    wcel
    wph
    cS
    @10
    @19
    cnmbfm.2
    wph
    @9
    @12
    @10
    @19
    wcel
    cnmbfm.1
    @13
    cJ
    ctop
    sigagensiga
    3syl
    eqeltrd
    cS
    @6
    elrnsiga
    syl
    cnmbfm.3
    imambfm
    mpbir2and
end
