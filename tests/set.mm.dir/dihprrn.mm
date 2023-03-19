include "cpr.mm"
include "cfv.mm"
include "crn.mm"
include "wcel.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "prcom.mm"
include "preq2.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lsppr0.mm"
include "sylan9eqr.mm"
include "chlt.mm"
include "dihlsprn.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "simprl.mm"
include "simprr.mm"
include "dihprrnlem2.mm"
include "pm2.61da2ne.mm"

theorem dihprrn
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihprrn.h: |- H = ( LHyp ` K )
  assume dihprrn.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihprrn.v: |- V = ( Base ` U )
  assume dihprrn.n: |- N = ( LSpan ` U )
  assume dihprrn.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihprrn.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihprrn.x: |- ( ph -> X e. V )
  assume dihprrn.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( N ` { X , Y } ) e. ran I )

  proof
    wph
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    cI
    crn
    #
    wcel
    cX
    cU
    c0g
    cfv
    #
    cY
    @3
    wph
    cX
    @3
    wceq
    #
    wa
    @1
    cY
    csn
    cN
    cfv
    #
    @2
    @4
    wph
    @1
    cY
    @3
    cpr
    #
    cN
    cfv
    @5
    @4
    @0
    @6
    cN
    @4
    @0
    cY
    cX
    cpr
    @6
    cX
    cY
    prcom
    cX
    @3
    cY
    preq2
    syl5eq
    fveq2d
    wph
    cN
    cV
    cU
    cY
    @3
    dihprrn.v
    @3
    eqid
    #
    dihprrn.n
    wph
    cU
    cH
    cK
    cW
    dihprrn.h
    dihprrn.u
    dihprrn.k
    dvhlmod
    #
    dihprrn.y
    lsppr0
    sylan9eqr
    wph
    @5
    @2
    wcel
    #
    @4
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cY
    cV
    wcel
    #
    @9
    dihprrn.k
    dihprrn.y
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cY
    dihprrn.h
    dihprrn.u
    dihprrn.v
    dihprrn.n
    dihprrn.i
    dihlsprn
    syl2anc
    adantr
    eqeltrd
    wph
    cY
    @3
    wceq
    #
    wa
    @1
    cX
    csn
    cN
    cfv
    #
    @2
    @12
    wph
    @1
    cX
    @3
    cpr
    #
    cN
    cfv
    @13
    @12
    @0
    @14
    cN
    cY
    @3
    cX
    preq2
    fveq2d
    wph
    cN
    cV
    cU
    cX
    @3
    dihprrn.v
    @7
    dihprrn.n
    @8
    dihprrn.x
    lsppr0
    sylan9eqr
    wph
    @13
    @2
    wcel
    #
    @12
    wph
    @10
    cX
    cV
    wcel
    #
    @15
    dihprrn.k
    dihprrn.x
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cX
    dihprrn.h
    dihprrn.u
    dihprrn.v
    dihprrn.n
    dihprrn.i
    dihlsprn
    syl2anc
    adantr
    eqeltrd
    wph
    cX
    @3
    wne
    #
    cY
    @3
    wne
    #
    wa
    #
    wa
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cX
    cY
    @3
    dihprrn.h
    dihprrn.u
    dihprrn.v
    dihprrn.n
    dihprrn.i
    wph
    @10
    @19
    dihprrn.k
    adantr
    wph
    @16
    @19
    dihprrn.x
    adantr
    wph
    @11
    @19
    dihprrn.y
    adantr
    @7
    wph
    @17
    @18
    simprl
    wph
    @17
    @18
    simprr
    dihprrnlem2
    pm2.61da2ne
end
