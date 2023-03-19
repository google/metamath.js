include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "dvh2dim.mm"
include "adantr.mm"
include "prcom.mm"
include "preq2.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lsppr0.mm"
include "sylan9eqr.mm"
include "eleq2d.mm"
include "notbid.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "wne.mm"
include "chlt.mm"
include "simprl.mm"
include "simprr.mm"
include "dvhdimlem.mm"
include "pm2.61da2ne.mm"

theorem dvh3dim
  let wph: wff ph
  let vz: setvar z
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let c.0: class .0.
  let cZ: class Z
  assume dvh3dim.h: |- H = ( LHyp ` K )
  assume dvh3dim.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh3dim.v: |- V = ( Base ` U )
  assume dvh3dim.n: |- N = ( LSpan ` U )
  assume dvh3dim.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dvh3dim.x: |- ( ph -> X e. V )
  assume dvh3dim.y: |- ( ph -> Y e. V )

  disjoint N z
  disjoint U z
  disjoint V z
  disjoint X z
  disjoint Y z
  disjoint ph z
  disjoint K p
  disjoint p z
  disjoint N p
  disjoint .0. p
  disjoint .0. z
  disjoint U p
  disjoint V p
  disjoint W p
  disjoint X p
  disjoint Y p
  disjoint Z p
  disjoint Z z
  disjoint p ph
  assert |- ( ph -> E. z e. V -. z e. ( N ` { X , Y } ) )

  proof
    wph
    vz
    cv
    #
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vz
    cV
    wrex
    #
    cX
    cU
    c0g
    cfv
    #
    cY
    @6
    wph
    cX
    @6
    wceq
    #
    wa
    #
    @5
    @0
    cY
    csn
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vz
    cV
    wrex
    #
    wph
    @12
    @7
    wph
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cY
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    dvh3dim.k
    dvh3dim.y
    dvh2dim
    adantr
    @8
    @4
    @11
    vz
    cV
    @8
    @3
    @10
    @8
    @2
    @9
    @0
    @7
    wph
    @2
    cY
    @6
    cpr
    #
    cN
    cfv
    @9
    @7
    @1
    @13
    cN
    @7
    @1
    cY
    cX
    cpr
    @13
    cX
    cY
    prcom
    cX
    @6
    cY
    preq2
    syl5eq
    fveq2d
    wph
    cN
    cV
    cU
    cY
    @6
    dvh3dim.v
    @6
    eqid
    #
    dvh3dim.n
    wph
    cU
    cH
    cK
    cW
    dvh3dim.h
    dvh3dim.u
    dvh3dim.k
    dvhlmod
    #
    dvh3dim.y
    lsppr0
    sylan9eqr
    eleq2d
    notbid
    rexbidv
    mpbird
    wph
    cY
    @6
    wceq
    #
    wa
    #
    @5
    @0
    cX
    csn
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vz
    cV
    wrex
    #
    wph
    @21
    @16
    wph
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cX
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    dvh3dim.k
    dvh3dim.x
    dvh2dim
    adantr
    @17
    @4
    @20
    vz
    cV
    @17
    @3
    @19
    @17
    @2
    @18
    @0
    @16
    wph
    @2
    cX
    @6
    cpr
    #
    cN
    cfv
    @18
    @16
    @1
    @22
    cN
    cY
    @6
    cX
    preq2
    fveq2d
    wph
    cN
    cV
    cU
    cX
    @6
    dvh3dim.v
    @14
    dvh3dim.n
    @15
    dvh3dim.x
    lsppr0
    sylan9eqr
    eleq2d
    notbid
    rexbidv
    mpbird
    wph
    cX
    @6
    wne
    #
    cY
    @6
    wne
    #
    wa
    #
    wa
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cX
    cY
    @6
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @25
    dvh3dim.k
    adantr
    wph
    cX
    cV
    wcel
    @25
    dvh3dim.x
    adantr
    wph
    cY
    cV
    wcel
    @25
    dvh3dim.y
    adantr
    @14
    wph
    @23
    @24
    simprl
    wph
    @23
    @24
    simprr
    dvhdimlem
    pm2.61da2ne
end
