include "cv.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "cun.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "cfv.mm"
include "wss.mm"
include "adantr.mm"
include "cmre.mm"
include "simpr.mm"
include "ssun2.mm"
include "difundir.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "ssdifin0.mm"
include "syl.mm"
include "syl5eqr.mm"
include "minel.mm"
include "syl2anc.mm"
include "difsnb.mm"
include "sylib.mm"
include "uneq2d.mm"
include "syl5eq.mm"
include "syl5sseqr.mm"
include "mrissd.mm"
include "ssdifssd.mm"
include "mrcssidd.mm"
include "sstrd.mm"
include "unssd.mm"
include "mrcssvd.mm"
include "mrcssd.mm"
include "mrcidmd.mm"
include "sseqtrd.mm"
include "sseldd.mm"
include "ssun1.mm"
include "sseldi.mm"
include "ismri2dad.mm"
include "pm2.65da.mm"
include "nss.mm"
include "simprl.mm"
include "simprr.mm"
include "ssneldd.mm"
include "unass.mm"
include "wral.mm"
include "cpw.mm"
include "difss.mm"
include "unss1.mm"
include "mp1i.mm"
include "mrissmrid.mm"
include "difss2d.mm"
include "fveq2d.mm"
include "neleqtrd.mm"
include "mreexmrid.mm"
include "syl5eqelr.mm"
include "jca32.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"

theorem mreexexlem2d
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cX: class X
  let cY: class Y
  let vs: setvar s
  assume mreexexlem2d.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mreexexlem2d.2: |- N = ( mrCls ` A )
  assume mreexexlem2d.3: |- I = ( mrInd ` A )
  assume mreexexlem2d.4: |- ( ph -> A. s e. ~P X A. y e. X A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) ) y e. ( N ` ( s u. { z } ) ) )
  assume mreexexlem2d.5: |- ( ph -> F C_ ( X \ H ) )
  assume mreexexlem2d.6: |- ( ph -> G C_ ( X \ H ) )
  assume mreexexlem2d.7: |- ( ph -> F C_ ( N ` ( G u. H ) ) )
  assume mreexexlem2d.8: |- ( ph -> ( F u. H ) e. I )
  assume mreexexlem2d.9: |- ( ph -> Y e. F )

  disjoint F s
  disjoint g s
  disjoint s y
  disjoint s z
  disjoint F g
  disjoint F y
  disjoint F z
  disjoint g y
  disjoint g z
  disjoint y z
  disjoint G s
  disjoint G g
  disjoint G y
  disjoint G z
  disjoint H s
  disjoint H g
  disjoint H y
  disjoint H z
  disjoint ph s
  disjoint g ph
  disjoint ph y
  disjoint ph z
  disjoint Y s
  disjoint Y g
  disjoint Y y
  disjoint Y z
  disjoint N s
  disjoint N g
  disjoint N y
  disjoint N z
  disjoint X s
  disjoint X y
  assert |- ( ph -> E. g e. G ( -. g e. ( F \ { Y } ) /\ ( ( F \ { Y } ) u. ( H u. { g } ) ) e. I ) )

  proof
    wph
    vg
    cv
    #
    cG
    wcel
    #
    @0
    cF
    cY
    csn
    #
    cdif
    #
    wcel
    wn
    #
    @3
    cH
    @0
    csn
    #
    cun
    cun
    #
    cI
    wcel
    #
    wa
    #
    wa
    #
    vg
    wex
    #
    @8
    vg
    cG
    wrex
    wph
    @1
    @0
    cF
    cH
    cun
    #
    @2
    cdif
    #
    cN
    cfv
    #
    wcel
    wn
    #
    wa
    #
    vg
    wex
    #
    @10
    wph
    cG
    @13
    wss
    #
    wn
    @16
    wph
    @17
    cY
    @13
    wcel
    wph
    @17
    wa
    #
    cF
    @13
    cY
    @18
    cF
    cG
    cH
    cun
    #
    cN
    cfv
    #
    @13
    wph
    cF
    @20
    wss
    @17
    mreexexlem2d.7
    adantr
    @18
    @20
    @13
    cN
    cfv
    @13
    @18
    cA
    @19
    cN
    @13
    cX
    wph
    cA
    cX
    cmre
    cfv
    wcel
    #
    @17
    mreexexlem2d.1
    adantr
    #
    mreexexlem2d.2
    @18
    cG
    cH
    @13
    wph
    @17
    simpr
    wph
    cH
    @13
    wss
    @17
    wph
    cH
    @12
    @13
    wph
    @3
    cH
    cun
    #
    cH
    @12
    cH
    @3
    ssun2
    wph
    @12
    @3
    cH
    @2
    cdif
    #
    cun
    @23
    cF
    cH
    @2
    difundir
    wph
    @24
    cH
    @3
    wph
    cY
    cH
    wcel
    wn
    #
    @24
    cH
    wceq
    wph
    cY
    cF
    wcel
    #
    cH
    cF
    cin
    #
    c0
    wceq
    @25
    mreexexlem2d.9
    wph
    @27
    cF
    cH
    cin
    #
    c0
    cF
    cH
    incom
    wph
    cF
    cX
    cH
    cdif
    #
    wss
    @28
    c0
    wceq
    mreexexlem2d.5
    cF
    cX
    cH
    ssdifin0
    syl
    syl5eqr
    cY
    cF
    cH
    minel
    syl2anc
    cY
    cH
    difsnb
    sylib
    uneq2d
    syl5eq
    #
    syl5sseqr
    wph
    cA
    @12
    cN
    cX
    mreexexlem2d.1
    mreexexlem2d.2
    wph
    @11
    cX
    @2
    wph
    cA
    @11
    cI
    cX
    mreexexlem2d.3
    mreexexlem2d.1
    mreexexlem2d.8
    mrissd
    ssdifssd
    #
    mrcssidd
    #
    sstrd
    adantr
    unssd
    @18
    cA
    @12
    cN
    cX
    @22
    mreexexlem2d.2
    mrcssvd
    mrcssd
    @18
    cA
    @12
    cN
    cX
    @22
    mreexexlem2d.2
    wph
    @12
    cX
    wss
    @17
    @31
    adantr
    mrcidmd
    sseqtrd
    sstrd
    wph
    @26
    @17
    mreexexlem2d.9
    adantr
    #
    sseldd
    @18
    cA
    @11
    cI
    cN
    cX
    cY
    mreexexlem2d.2
    mreexexlem2d.3
    @22
    wph
    @11
    cI
    wcel
    #
    @17
    mreexexlem2d.8
    adantr
    @18
    cF
    @11
    cY
    cF
    cH
    ssun1
    @33
    sseldi
    ismri2dad
    pm2.65da
    vg
    cG
    @13
    nss
    sylib
    wph
    @15
    @9
    vg
    wph
    @15
    @9
    wph
    @15
    wa
    #
    @1
    @4
    @7
    wph
    @1
    @14
    simprl
    #
    @35
    @3
    @13
    @0
    wph
    @3
    @13
    wss
    @15
    wph
    @3
    @12
    @13
    wph
    @23
    @3
    @12
    @3
    cH
    ssun1
    @30
    syl5sseqr
    @32
    sstrd
    adantr
    wph
    @1
    @14
    simprr
    #
    ssneldd
    @35
    @6
    @23
    @5
    cun
    cI
    @3
    cH
    @5
    unass
    @35
    vy
    vz
    cA
    @23
    cI
    cN
    cX
    @0
    vs
    wph
    @21
    @15
    mreexexlem2d.1
    adantr
    #
    mreexexlem2d.2
    mreexexlem2d.3
    wph
    vy
    cv
    #
    vs
    cv
    #
    vz
    cv
    csn
    cun
    cN
    cfv
    wcel
    vz
    @40
    @39
    csn
    cun
    cN
    cfv
    @40
    cN
    cfv
    cdif
    wral
    vy
    cX
    wral
    vs
    cX
    cpw
    wral
    @15
    mreexexlem2d.4
    adantr
    @35
    cA
    @11
    @23
    cI
    cN
    cX
    @38
    mreexexlem2d.2
    mreexexlem2d.3
    wph
    @34
    @15
    mreexexlem2d.8
    adantr
    @3
    cF
    wss
    @23
    @11
    wss
    @35
    cF
    @2
    difss
    @3
    cF
    cH
    unss1
    mp1i
    mrissmrid
    @35
    cG
    cX
    @0
    @35
    cG
    cX
    cH
    wph
    cG
    @29
    wss
    @15
    mreexexlem2d.6
    adantr
    difss2d
    @36
    sseldd
    @35
    @13
    @23
    cN
    cfv
    @0
    @37
    @35
    @12
    @23
    cN
    wph
    @12
    @23
    wceq
    @15
    @30
    adantr
    fveq2d
    neleqtrd
    mreexmrid
    syl5eqelr
    jca32
    ex
    eximdv
    mpd
    @8
    vg
    cG
    df-rex
    sylibr
end
