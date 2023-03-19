include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
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
include "cvv.mm"
include "wa.mm"
include "istrkgc.mm"
include "simprbi.mm"
include "simprd.mm"
include "syl.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "eqeq2.mm"
include "id.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "imbi1d.mm"
include "rspc3v.mm"
include "syl3anc.mm"
include "mp2d.mm"

theorem axtgcgrid
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
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
  let cV: class V
  assume axtrkg.p: |- P = ( Base ` G )
  assume axtrkg.d: |- .- = ( dist ` G )
  assume axtrkg.i: |- I = ( Itv ` G )
  assume axtrkg.g: |- ( ph -> G e. TarskiG )
  assume axtgcgrid.1: |- ( ph -> X e. P )
  assume axtgcgrid.2: |- ( ph -> Y e. P )
  assume axtgcgrid.3: |- ( ph -> Z e. P )
  assume axtgcgrid.4: |- ( ph -> ( X .- Y ) = ( Z .- Z ) )


  assert |- ( ph -> X = Y )

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
    vz
    cv
    #
    @3
    c.mi
    co
    #
    wceq
    #
    @0
    @1
    wceq
    #
    wi
    #
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
    cX
    cY
    c.mi
    co
    #
    cZ
    cZ
    c.mi
    co
    #
    wceq
    #
    cX
    cY
    wceq
    #
    wph
    cG
    cstrkgc
    wcel
    #
    @8
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
    @16
    @0
    csn
    cdif
    @3
    @0
    @1
    vi
    cv
    #
    co
    wcel
    @0
    @3
    @1
    @17
    co
    wcel
    @1
    @0
    @3
    @17
    co
    wcel
    w3o
    vz
    @16
    crab
    cmpt2
    wceq
    vi
    @15
    citv
    cfv
    wsbc
    vp
    @15
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
    @19
    @14
    cstrkgc
    @14
    @18
    inss1
    cstrkgc
    cstrkgb
    inss1
    sstri
    eqsstri
    axtrkg.g
    sseldi
    @13
    @2
    @1
    @0
    c.mi
    co
    wceq
    vy
    cP
    wral
    vx
    cP
    wral
    #
    @8
    @13
    cG
    cvv
    wcel
    @20
    @8
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
    simprd
    syl
    axtgcgrid.4
    wph
    cX
    cP
    wcel
    cY
    cP
    wcel
    cZ
    cP
    wcel
    @8
    @11
    @12
    wi
    #
    wi
    axtgcgrid.1
    axtgcgrid.2
    axtgcgrid.3
    @7
    @21
    cX
    @1
    c.mi
    co
    #
    @4
    wceq
    #
    cX
    @1
    wceq
    #
    wi
    @9
    @4
    wceq
    #
    @12
    wi
    vx
    vy
    vz
    cX
    cY
    cZ
    cP
    cP
    cP
    @0
    cX
    wceq
    #
    @5
    @23
    @6
    @24
    @26
    @2
    @22
    @4
    @0
    cX
    @1
    c.mi
    oveq1
    eqeq1d
    @0
    cX
    @1
    eqeq1
    imbi12d
    @1
    cY
    wceq
    #
    @23
    @25
    @24
    @12
    @27
    @22
    @9
    @4
    @1
    cY
    cX
    c.mi
    oveq2
    eqeq1d
    @1
    cY
    cX
    eqeq2
    imbi12d
    @3
    cZ
    wceq
    #
    @25
    @11
    @12
    @28
    @4
    @10
    @9
    @28
    @3
    cZ
    @3
    cZ
    c.mi
    @28
    id
    #
    @29
    oveq12d
    eqeq2d
    imbi1d
    rspc3v
    syl3anc
    mp2d
end
