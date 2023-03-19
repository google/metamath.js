include "cv.mm"
include "co.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "preq2.mm"
include "fveq2d.mm"
include "clvec.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "eldifad.mm"
include "lsppr0.mm"
include "sylan9eqr.mm"
include "wss.mm"
include "prssi.mm"
include "syl2anc.mm"
include "snsspr1.mm"
include "a1i.mm"
include "lspss.mm"
include "syl3anc.mm"
include "adantr.mm"
include "eqsstrd.mm"
include "ssneldd.mm"
include "wne.mm"
include "clsm.mm"
include "cdif.mm"
include "simpr.mm"
include "mapdindp0.mm"
include "oveq2d.mm"
include "eqid.mm"
include "lmodvacl.mm"
include "lsmpr.mm"
include "3eqtr4d.mm"
include "neleqtrrd.mm"
include "pm2.61dane.mm"

theorem mapdindp2
  let wph: wff ph
  let vw: setvar w
  let c.pl: class .+
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume mapdindp1.v: |- V = ( Base ` W )
  assume mapdindp1.p: |- .+ = ( +g ` W )
  assume mapdindp1.o: |- .0. = ( 0g ` W )
  assume mapdindp1.n: |- N = ( LSpan ` W )
  assume mapdindp1.w: |- ( ph -> W e. LVec )
  assume mapdindp1.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdindp1.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdindp1.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdindp1.W: |- ( ph -> w e. ( V \ { .0. } ) )
  assume mapdindp1.e: |- ( ph -> ( N ` { Y } ) = ( N ` { Z } ) )
  assume mapdindp1.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume mapdindp1.f: |- ( ph -> -. w e. ( N ` { X , Y } ) )


  assert |- ( ph -> -. w e. ( N ` { X , ( Y .+ Z ) } ) )

  proof
    wph
    vw
    cv
    #
    cX
    cY
    cZ
    c.pl
    co
    #
    cpr
    #
    cN
    cfv
    #
    wcel
    wn
    @1
    c.0
    wph
    @1
    c.0
    wceq
    #
    wa
    #
    @3
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    @0
    @5
    @3
    cX
    csn
    #
    cN
    cfv
    #
    @7
    @4
    wph
    @3
    cX
    c.0
    cpr
    #
    cN
    cfv
    @9
    @4
    @2
    @10
    cN
    @1
    c.0
    cX
    preq2
    fveq2d
    wph
    cN
    cV
    cW
    cX
    c.0
    mapdindp1.v
    mapdindp1.o
    mapdindp1.n
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    #
    mapdindp1.w
    cW
    lveclmod
    syl
    #
    wph
    cX
    cV
    c.0
    csn
    #
    mapdindp1.x
    eldifad
    #
    lsppr0
    sylan9eqr
    wph
    @9
    @7
    wss
    #
    @4
    wph
    @12
    @6
    cV
    wss
    #
    @8
    @6
    wss
    #
    @16
    @13
    wph
    cX
    cV
    wcel
    cY
    cV
    wcel
    #
    @17
    @15
    wph
    cY
    cV
    @14
    mapdindp1.y
    eldifad
    #
    cX
    cY
    cV
    prssi
    syl2anc
    @18
    wph
    cX
    cY
    snsspr1
    a1i
    @8
    @6
    cN
    cV
    cW
    mapdindp1.v
    mapdindp1.n
    lspss
    syl3anc
    adantr
    eqsstrd
    wph
    @0
    @7
    wcel
    wn
    #
    @4
    mapdindp1.f
    adantr
    ssneldd
    wph
    @1
    c.0
    wne
    #
    wa
    #
    @3
    @7
    @0
    wph
    @21
    @22
    mapdindp1.f
    adantr
    #
    @23
    @9
    @1
    csn
    cN
    cfv
    #
    cW
    clsm
    cfv
    #
    co
    #
    @9
    cY
    csn
    cN
    cfv
    #
    @26
    co
    #
    @3
    @7
    @23
    @25
    @28
    @9
    @26
    @23
    vw
    c.pl
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    mapdindp1.v
    mapdindp1.p
    mapdindp1.o
    mapdindp1.n
    wph
    @11
    @22
    mapdindp1.w
    adantr
    wph
    cX
    cV
    @14
    cdif
    #
    wcel
    @22
    mapdindp1.x
    adantr
    wph
    cY
    @30
    wcel
    @22
    mapdindp1.y
    adantr
    wph
    cZ
    @30
    wcel
    @22
    mapdindp1.z
    adantr
    wph
    @0
    @30
    wcel
    @22
    mapdindp1.W
    adantr
    wph
    @28
    cZ
    csn
    cN
    cfv
    wceq
    @22
    mapdindp1.e
    adantr
    wph
    @9
    @28
    wne
    @22
    mapdindp1.ne
    adantr
    @24
    wph
    @22
    simpr
    mapdindp0
    oveq2d
    wph
    @3
    @27
    wceq
    @22
    wph
    @26
    cN
    cV
    cW
    cX
    @1
    mapdindp1.v
    mapdindp1.n
    @26
    eqid
    #
    @13
    @15
    wph
    @12
    @19
    cZ
    cV
    wcel
    @1
    cV
    wcel
    @13
    @20
    wph
    cZ
    cV
    @14
    mapdindp1.z
    eldifad
    c.pl
    cV
    cW
    cY
    cZ
    mapdindp1.v
    mapdindp1.p
    lmodvacl
    syl3anc
    lsmpr
    adantr
    wph
    @7
    @29
    wceq
    @22
    wph
    @26
    cN
    cV
    cW
    cX
    cY
    mapdindp1.v
    mapdindp1.n
    @31
    @13
    @15
    @20
    lsmpr
    adantr
    3eqtr4d
    neleqtrrd
    pm2.61dane
end
