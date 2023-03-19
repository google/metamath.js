include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cstrkgc.mm"
include "wcel.mm"
include "cstrkg.mm"
include "cstrkgb.mm"
include "cin.mm"
include "cstrkgcb.mm"
include "clng.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "w3o.mm"
include "crab.mm"
include "cmpt2.mm"
include "citv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cab.mm"
include "df-trkg.mm"
include "inss1.mm"
include "sstri.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "wi.mm"
include "cvv.mm"
include "wa.mm"
include "istrkgc.mm"
include "simprbi.mm"
include "simpld.mm"
include "syl.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "mpd.mm"

theorem axtgcgrrflx
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let cS: class S
  let cT: class T
  let cU: class U
  let cZ: class Z
  let cV: class V
  assume axtrkg.p: |- P = ( Base ` G )
  assume axtrkg.d: |- .- = ( dist ` G )
  assume axtrkg.i: |- I = ( Itv ` G )
  assume axtrkg.g: |- ( ph -> G e. TarskiG )
  assume axtgcgrrflx.1: |- ( ph -> X e. P )
  assume axtgcgrrflx.2: |- ( ph -> Y e. P )


  assert |- ( ph -> ( X .- Y ) = ( Y .- X ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    c.mi
    co
    #
    @1
    @0
    c.mi
    co
    #
    wceq
    #
    vy
    cP
    wral
    vx
    cP
    wral
    #
    cX
    cY
    c.mi
    co
    #
    cY
    cX
    c.mi
    co
    #
    wceq
    #
    wph
    cG
    cstrkgc
    wcel
    #
    @5
    wph
    cstrkg
    cstrkgc
    cG
    cstrkg
    cstrkgc
    cstrkgb
    cin
    #
    cstrkgcb
    vf
    cv
    #
    clng
    cfv
    vx
    vy
    vp
    cv
    #
    @12
    @0
    csn
    cdif
    vz
    cv
    #
    @0
    @1
    vi
    cv
    #
    co
    wcel
    @0
    @13
    @1
    @14
    co
    wcel
    @1
    @0
    @13
    @14
    co
    wcel
    w3o
    vz
    @12
    crab
    cmpt2
    wceq
    vi
    @11
    citv
    cfv
    wsbc
    vp
    @11
    cbs
    cfv
    wsbc
    vf
    cab
    cin
    #
    cin
    #
    cstrkgc
    vx
    vy
    vz
    vf
    vi
    vp
    df-trkg
    @16
    @10
    cstrkgc
    @10
    @15
    inss1
    cstrkgc
    cstrkgb
    inss1
    sstri
    eqsstri
    axtrkg.g
    sseldi
    @9
    @5
    @2
    @13
    @13
    c.mi
    co
    wceq
    @0
    @1
    wceq
    wi
    vz
    cP
    wral
    vy
    cP
    wral
    vx
    cP
    wral
    #
    @9
    cG
    cvv
    wcel
    @5
    @17
    wa
    vx
    vy
    vz
    cP
    cG
    cI
    c.mi
    axtrkg.p
    axtrkg.d
    axtrkg.i
    istrkgc
    simprbi
    simpld
    syl
    wph
    cX
    cP
    wcel
    cY
    cP
    wcel
    @5
    @8
    wi
    axtgcgrrflx.1
    axtgcgrrflx.2
    @4
    @8
    cX
    @1
    c.mi
    co
    #
    @1
    cX
    c.mi
    co
    #
    wceq
    vx
    vy
    cX
    cY
    cP
    cP
    @0
    cX
    wceq
    @2
    @18
    @3
    @19
    @0
    cX
    @1
    c.mi
    oveq1
    @0
    cX
    @1
    c.mi
    oveq2
    eqeq12d
    @1
    cY
    wceq
    @18
    @6
    @19
    @7
    @1
    cY
    cX
    c.mi
    oveq2
    @1
    cY
    cX
    c.mi
    oveq1
    eqeq12d
    rspc2v
    syl2anc
    mpd
end
