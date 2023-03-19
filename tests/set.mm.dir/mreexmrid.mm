include "csn.mm"
include "cun.mm"
include "mrissd.mm"
include "snssd.mm"
include "unssd.mm"
include "cv.mm"
include "cdif.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "w3a.mm"
include "cvv.mm"
include "cmre.mm"
include "3ad2ant1.mm"
include "elfvexd.mm"
include "wral.mm"
include "cpw.mm"
include "ssdifssd.mm"
include "simp3.mm"
include "difundir.mm"
include "wceq.mm"
include "simp2.mm"
include "mrcssidd.mm"
include "ssneldd.mm"
include "nelneq.mm"
include "syl2anc.mm"
include "elsni.mm"
include "nsyl.mm"
include "difsnb.mm"
include "sylib.mm"
include "uneq2d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "ismri2dad.mm"
include "mreexd.mm"
include "undif1.mm"
include "wss.mm"
include "ssequn2.mm"
include "neleqtrrd.mm"
include "pm2.65i.mm"
include "df-3an.mm"
include "mtbi.mm"
include "imnani.mm"
include "adantlr.mm"
include "adantl.mm"
include "ad2antrr.mm"
include "eqneltrd.mm"
include "sneqd.mm"
include "difeq2d.mm"
include "difun2.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "wo.mm"
include "simpr.mm"
include "elun.mm"
include "mpjaodan.mm"
include "ralrimiva.mm"
include "ismri2dd.mm"

theorem mreexmrid
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cS: class S
  let cI: class I
  let cN: class N
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vx: setvar x
  assume mreexmrid.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mreexmrid.2: |- N = ( mrCls ` A )
  assume mreexmrid.3: |- I = ( mrInd ` A )
  assume mreexmrid.4: |- ( ph -> A. s e. ~P X A. y e. X A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) ) y e. ( N ` ( s u. { z } ) ) )
  assume mreexmrid.5: |- ( ph -> S e. I )
  assume mreexmrid.6: |- ( ph -> Y e. X )
  assume mreexmrid.7: |- ( ph -> -. Y e. ( N ` S ) )

  disjoint X s
  disjoint s y
  disjoint X y
  disjoint S s
  disjoint s z
  disjoint S y
  disjoint S z
  disjoint y z
  disjoint ph s
  disjoint ph y
  disjoint ph z
  disjoint Y s
  disjoint Y y
  disjoint Y z
  disjoint N s
  disjoint N y
  disjoint N z
  disjoint A x
  disjoint s x
  disjoint S x
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint Y x
  assert |- ( ph -> ( S u. { Y } ) e. I )

  proof
    wph
    vx
    cA
    cS
    cY
    csn
    #
    cun
    #
    cI
    cN
    cX
    mreexmrid.2
    mreexmrid.3
    mreexmrid.1
    wph
    cS
    @0
    cX
    wph
    cA
    cS
    cI
    cX
    mreexmrid.3
    mreexmrid.1
    mreexmrid.5
    mrissd
    #
    wph
    cY
    cX
    mreexmrid.6
    snssd
    unssd
    wph
    vx
    cv
    #
    @1
    @3
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    @1
    wph
    @3
    @1
    wcel
    #
    wa
    #
    @3
    cS
    wcel
    #
    @8
    @3
    @0
    wcel
    #
    wph
    @11
    @8
    @9
    wph
    @11
    wa
    #
    @7
    wph
    @11
    @7
    w3a
    #
    @13
    @7
    wa
    @14
    cY
    cS
    @4
    cdif
    #
    @4
    cun
    #
    cN
    cfv
    #
    wcel
    @14
    vy
    vz
    @15
    cN
    cvv
    cX
    cY
    @3
    vs
    @14
    cA
    cmre
    cX
    wph
    @11
    cA
    cX
    cmre
    cfv
    wcel
    @7
    mreexmrid.1
    3ad2ant1
    #
    elfvexd
    wph
    @11
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
    @20
    @19
    csn
    cun
    cN
    cfv
    @20
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
    @7
    mreexmrid.4
    3ad2ant1
    @14
    cS
    cX
    @4
    @14
    cA
    cS
    cI
    cX
    mreexmrid.3
    @18
    wph
    @11
    cS
    cI
    wcel
    @7
    mreexmrid.5
    3ad2ant1
    #
    mrissd
    ssdifssd
    wph
    @11
    cY
    cX
    wcel
    @7
    mreexmrid.6
    3ad2ant1
    @14
    @3
    @6
    @15
    @0
    cun
    #
    cN
    cfv
    wph
    @11
    @7
    simp3
    @14
    @5
    @22
    cN
    @14
    @5
    @15
    @0
    @4
    cdif
    #
    cun
    @22
    cS
    @0
    @4
    difundir
    @14
    @23
    @0
    @15
    @14
    @12
    wn
    @23
    @0
    wceq
    @14
    @3
    cY
    wceq
    #
    @12
    @14
    @11
    cY
    cS
    wcel
    wn
    #
    @24
    wn
    wph
    @11
    @7
    simp2
    #
    wph
    @11
    @25
    @7
    wph
    cS
    cS
    cN
    cfv
    #
    cY
    wph
    cA
    cS
    cN
    cX
    mreexmrid.1
    mreexmrid.2
    @2
    mrcssidd
    mreexmrid.7
    ssneldd
    #
    3ad2ant1
    @3
    cY
    cS
    nelneq
    syl2anc
    @3
    cY
    elsni
    #
    nsyl
    @3
    @0
    difsnb
    sylib
    uneq2d
    syl5eq
    fveq2d
    eleqtrd
    @14
    cA
    cS
    cI
    cN
    cX
    @3
    mreexmrid.2
    mreexmrid.3
    @18
    @21
    @26
    ismri2dad
    mreexd
    @14
    @17
    @27
    cY
    wph
    @11
    cY
    @27
    wcel
    wn
    #
    @7
    mreexmrid.7
    3ad2ant1
    @14
    @16
    cS
    cN
    @14
    @16
    cS
    @4
    cun
    #
    cS
    cS
    @4
    undif1
    @14
    @4
    cS
    wss
    @31
    cS
    wceq
    @14
    @3
    cS
    @26
    snssd
    @4
    cS
    ssequn2
    sylib
    syl5eq
    fveq2d
    neleqtrrd
    pm2.65i
    wph
    @11
    @7
    df-3an
    mtbi
    imnani
    adantlr
    @10
    @12
    wa
    #
    @6
    @27
    @3
    @32
    @3
    cY
    @27
    @12
    @24
    @10
    @29
    adantl
    #
    wph
    @30
    @9
    @12
    mreexmrid.7
    ad2antrr
    eqneltrd
    @32
    @5
    cS
    cN
    @32
    @5
    cS
    @0
    cdif
    #
    cS
    @32
    @5
    @1
    @0
    cdif
    @34
    @32
    @4
    @0
    @1
    @32
    @3
    cY
    @33
    sneqd
    difeq2d
    cS
    @0
    difun2
    syl6eq
    wph
    @34
    cS
    wceq
    #
    @9
    @12
    wph
    @25
    @35
    @28
    cY
    cS
    difsnb
    sylib
    ad2antrr
    eqtrd
    fveq2d
    neleqtrrd
    @10
    @9
    @11
    @12
    wo
    wph
    @9
    simpr
    @3
    cS
    @0
    elun
    sylib
    mpjaodan
    ralrimiva
    ismri2dd
end
