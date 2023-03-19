include "wcel.mm"
include "cv.mm"
include "wpss.mm"
include "cfv.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "w3a.mm"
include "wn.mm"
include "wex.mm"
include "pssnel.mm"
include "3ad2ant3.mm"
include "csn.mm"
include "cdif.mm"
include "cmre.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "wceq.mm"
include "simprr.mm"
include "difsnb.mm"
include "sylib.mm"
include "simpl3.mm"
include "pssssd.mm"
include "ssdifd.mm"
include "eqsstr3d.mm"
include "simpl2.mm"
include "mrissd.mm"
include "ssdifssd.mm"
include "mrcssd.mm"
include "difssd.mm"
include "mrcssidd.mm"
include "simprl.mm"
include "sseldd.mm"
include "ismri2dad.mm"
include "ssnelpssd.mm"
include "sspsstrd.mm"
include "exlimddv.mm"
include "3expia.mm"
include "alrimiv.mm"
include "ex.mm"
include "wral.mm"
include "wne.mm"
include "cvv.mm"
include "elfvexd.mm"
include "wss.mm"
include "ssexd.mm"
include "difexg.mm"
include "syl.mm"
include "simp1r.mm"
include "difsnpss.mm"
include "simp2.mm"
include "psseq1d.mm"
include "mpbird.mm"
include "simp3.mm"
include "mpd.mm"
include "fveq2d.mm"
include "mpbid.mm"
include "spcimdv.mm"
include "3impia.mm"
include "pssned.mm"
include "3com23.mm"
include "mrieqvlemd.mm"
include "necon3bbid.mm"
include "ralrimiv.mm"
include "ismri2d.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem mrieqv2d
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cI: class I
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vx: setvar x
  assume mrieqvd.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mrieqvd.2: |- N = ( mrCls ` A )
  assume mrieqvd.3: |- I = ( mrInd ` A )
  assume mrieqvd.4: |- ( ph -> S C_ X )

  disjoint S s
  disjoint ph s
  disjoint I s
  disjoint N s
  disjoint A x
  disjoint S x
  disjoint ph x
  disjoint s x
  disjoint I x
  disjoint N x
  assert |- ( ph -> ( S e. I <-> A. s ( s C. S -> ( N ` s ) C. ( N ` S ) ) ) )

  proof
    wph
    cS
    cI
    wcel
    #
    vs
    cv
    #
    cS
    wpss
    #
    @1
    cN
    cfv
    #
    cS
    cN
    cfv
    #
    wpss
    #
    wi
    #
    vs
    wal
    #
    wph
    @0
    @7
    wph
    @0
    wa
    @6
    vs
    wph
    @0
    @2
    @5
    wph
    @0
    @2
    w3a
    #
    vx
    cv
    #
    cS
    wcel
    #
    @9
    @1
    wcel
    wn
    #
    wa
    #
    @5
    vx
    @2
    wph
    @12
    vx
    wex
    @0
    vx
    @1
    cS
    pssnel
    3ad2ant3
    @8
    @12
    wa
    #
    @3
    cS
    @9
    csn
    #
    cdif
    #
    cN
    cfv
    #
    @4
    @13
    cA
    @1
    cN
    @15
    cX
    @8
    cA
    cX
    cmre
    cfv
    wcel
    #
    @12
    wph
    @0
    @17
    @2
    mrieqvd.1
    3ad2ant1
    adantr
    #
    mrieqvd.2
    @13
    @1
    @1
    @14
    cdif
    #
    @15
    @13
    @11
    @19
    @1
    wceq
    @8
    @10
    @11
    simprr
    @9
    @1
    difsnb
    sylib
    @13
    @1
    cS
    @14
    @13
    @1
    cS
    wph
    @0
    @2
    @12
    simpl3
    pssssd
    ssdifd
    eqsstr3d
    @13
    cS
    cX
    @14
    @13
    cA
    cS
    cI
    cX
    mrieqvd.3
    @18
    wph
    @0
    @2
    @12
    simpl2
    #
    mrissd
    #
    ssdifssd
    mrcssd
    @13
    @16
    @4
    @9
    @13
    cA
    @15
    cN
    cS
    cX
    @18
    mrieqvd.2
    @13
    cS
    @14
    difssd
    @21
    mrcssd
    @13
    cS
    @4
    @9
    @13
    cA
    cS
    cN
    cX
    @18
    mrieqvd.2
    @21
    mrcssidd
    @8
    @10
    @11
    simprl
    #
    sseldd
    @13
    cA
    cS
    cI
    cN
    cX
    @9
    mrieqvd.2
    mrieqvd.3
    @18
    @20
    @22
    ismri2dad
    ssnelpssd
    sspsstrd
    exlimddv
    3expia
    alrimiv
    ex
    wph
    @7
    @9
    @16
    wcel
    #
    wn
    #
    vx
    cS
    wral
    #
    @0
    wph
    @7
    @25
    wph
    @7
    wa
    @24
    vx
    cS
    wph
    @7
    @10
    @24
    wph
    @7
    @10
    w3a
    #
    @24
    @16
    @4
    wne
    #
    wph
    @10
    @7
    @27
    wph
    @10
    @7
    w3a
    @16
    @4
    wph
    @10
    @7
    @16
    @4
    wpss
    #
    wph
    @10
    wa
    #
    @6
    @28
    vs
    @15
    cvv
    @29
    cS
    cvv
    wcel
    @15
    cvv
    wcel
    @29
    cS
    cX
    cvv
    @29
    cA
    cmre
    cX
    wph
    @17
    @10
    mrieqvd.1
    adantr
    elfvexd
    wph
    cS
    cX
    wss
    #
    @10
    mrieqvd.4
    adantr
    ssexd
    cS
    @14
    cvv
    difexg
    syl
    @29
    @1
    @15
    wceq
    #
    @6
    @28
    @29
    @31
    @6
    w3a
    #
    @5
    @28
    @32
    @2
    @5
    @32
    @2
    @15
    cS
    wpss
    #
    @32
    @10
    @33
    wph
    @10
    @31
    @6
    simp1r
    @9
    cS
    difsnpss
    sylib
    @32
    @1
    @15
    cS
    @29
    @31
    @6
    simp2
    #
    psseq1d
    mpbird
    @29
    @31
    @6
    simp3
    mpd
    @32
    @3
    @16
    @4
    @32
    @1
    @15
    cN
    @34
    fveq2d
    psseq1d
    mpbid
    3expia
    spcimdv
    3impia
    pssned
    3com23
    @26
    @23
    @16
    @4
    @26
    cA
    cS
    cN
    cX
    @9
    wph
    @7
    @17
    @10
    mrieqvd.1
    3ad2ant1
    mrieqvd.2
    wph
    @7
    @30
    @10
    mrieqvd.4
    3ad2ant1
    wph
    @7
    @10
    simp3
    mrieqvlemd
    necon3bbid
    mpbird
    3expia
    ralrimiv
    ex
    wph
    vx
    cA
    cS
    cI
    cN
    cX
    mrieqvd.2
    mrieqvd.3
    mrieqvd.1
    mrieqvd.4
    ismri2d
    sylibrd
    impbid
end
