include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "wne.mm"
include "eqid.mm"
include "dvh1dim.mm"
include "adantr.mm"
include "simpr.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lspsn0.mm"
include "syl.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "velsn.mm"
include "syl6bb.mm"
include "necon3bbid.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "cpr.mm"
include "chlt.mm"
include "dvhdimlem.mm"
include "dfsn2.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "notbii.mm"
include "rexbii.mm"
include "sylibr.mm"
include "pm2.61dane.mm"

theorem dvh2dim
  let wph: wff ph
  let vz: setvar z
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vp: setvar p
  let c.0: class .0.
  let cY: class Y
  let cZ: class Z
  assume dvh3dim.h: |- H = ( LHyp ` K )
  assume dvh3dim.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh3dim.v: |- V = ( Base ` U )
  assume dvh3dim.n: |- N = ( LSpan ` U )
  assume dvh3dim.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dvh3dim.x: |- ( ph -> X e. V )

  disjoint N z
  disjoint U z
  disjoint V z
  disjoint X z
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
  disjoint Y z
  disjoint Z p
  disjoint Z z
  disjoint p ph
  assert |- ( ph -> E. z e. V -. z e. ( N ` { X } ) )

  proof
    wph
    vz
    cv
    #
    cX
    csn
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
    wph
    cX
    @6
    wceq
    #
    wa
    #
    @5
    @0
    @6
    wne
    #
    vz
    cV
    wrex
    #
    wph
    @10
    @7
    wph
    vz
    cU
    cH
    cK
    cV
    cW
    @6
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    @6
    eqid
    #
    dvh3dim.k
    dvh1dim
    adantr
    @8
    @4
    @9
    vz
    cV
    @8
    @3
    @0
    @6
    @8
    @3
    @0
    @6
    csn
    #
    wcel
    @0
    @6
    wceq
    @8
    @2
    @12
    @0
    @8
    @2
    @12
    cN
    cfv
    #
    @12
    @8
    @1
    @12
    cN
    @8
    cX
    @6
    wph
    @7
    simpr
    sneqd
    fveq2d
    wph
    @13
    @12
    wceq
    #
    @7
    wph
    cU
    clmod
    wcel
    @14
    wph
    cU
    cH
    cK
    cW
    dvh3dim.h
    dvh3dim.u
    dvh3dim.k
    dvhlmod
    cN
    cU
    @6
    @11
    dvh3dim.n
    lspsn0
    syl
    adantr
    eqtrd
    eleq2d
    vz
    @6
    velsn
    syl6bb
    necon3bbid
    rexbidv
    mpbird
    wph
    cX
    @6
    wne
    #
    wa
    #
    @0
    cX
    cX
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
    @5
    @16
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cX
    cX
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
    @15
    dvh3dim.k
    adantr
    wph
    cX
    cV
    wcel
    @15
    dvh3dim.x
    adantr
    #
    @21
    @11
    wph
    @15
    simpr
    #
    @22
    dvhdimlem
    @4
    @20
    vz
    cV
    @3
    @19
    @2
    @18
    @0
    @1
    @17
    cN
    cX
    dfsn2
    fveq2i
    eleq2i
    notbii
    rexbii
    sylibr
    pm2.61dane
end
