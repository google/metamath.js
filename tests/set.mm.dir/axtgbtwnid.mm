include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cstrkgb.mm"
include "cstrkg.mm"
include "cstrkgc.mm"
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
include "inss2.mm"
include "sstri.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "wa.mm"
include "wrex.mm"
include "cpw.mm"
include "cvv.mm"
include "w3a.mm"
include "istrkgb.mm"
include "simprbi.mm"
include "simp1d.mm"
include "syl.mm"
include "id.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "eleq1.mm"
include "eqeq2.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "mp2d.mm"

theorem axtgbtwnid
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
  assume axtgbtwnid.1: |- ( ph -> X e. P )
  assume axtgbtwnid.2: |- ( ph -> Y e. P )
  assume axtgbtwnid.3: |- ( ph -> Y e. ( X I X ) )


  assert |- ( ph -> X = Y )

  proof
    wph
    vy
    cv
    #
    vx
    cv
    #
    @1
    cI
    co
    #
    wcel
    #
    @1
    @0
    wceq
    #
    wi
    #
    vy
    cP
    wral
    vx
    cP
    wral
    #
    cY
    cX
    cX
    cI
    co
    #
    wcel
    #
    cX
    cY
    wceq
    #
    wph
    cG
    cstrkgb
    wcel
    #
    @6
    wph
    cstrkg
    cstrkgb
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
    @13
    @1
    csn
    cdif
    vz
    cv
    #
    @1
    @0
    vi
    cv
    #
    co
    wcel
    @1
    @14
    @0
    @15
    co
    wcel
    @0
    @1
    @14
    @15
    co
    wcel
    w3o
    vz
    @13
    crab
    cmpt2
    wceq
    vi
    @12
    citv
    cfv
    wsbc
    vp
    @12
    cbs
    cfv
    wsbc
    vf
    cab
    cin
    #
    cin
    #
    cstrkgb
    vx
    vy
    vz
    vf
    vi
    vp
    df-trkg
    @17
    @11
    cstrkgb
    @11
    @16
    inss1
    cstrkgc
    cstrkgb
    inss2
    sstri
    eqsstri
    axtrkg.g
    sseldi
    @10
    @6
    vu
    cv
    #
    @1
    @14
    cI
    co
    wcel
    vv
    cv
    #
    @0
    @14
    cI
    co
    wcel
    wa
    va
    cv
    #
    @18
    @0
    cI
    co
    wcel
    @20
    @19
    @1
    cI
    co
    wcel
    wa
    va
    cP
    wrex
    wi
    vv
    cP
    wral
    vu
    cP
    wral
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
    @1
    @20
    @0
    cI
    co
    wcel
    vy
    vt
    cv
    #
    wral
    vx
    vs
    cv
    #
    wral
    va
    cP
    wrex
    vb
    cv
    @1
    @0
    cI
    co
    wcel
    vy
    @22
    wral
    vx
    @23
    wral
    vb
    cP
    wrex
    wi
    vt
    cP
    cpw
    #
    wral
    vs
    @24
    wral
    #
    @10
    cG
    cvv
    wcel
    @6
    @21
    @25
    w3a
    vx
    vy
    vz
    vv
    vu
    vt
    cP
    cG
    cI
    c.mi
    vs
    va
    vb
    axtrkg.p
    axtrkg.d
    axtrkg.i
    istrkgb
    simprbi
    simp1d
    syl
    axtgbtwnid.3
    wph
    cX
    cP
    wcel
    cY
    cP
    wcel
    @6
    @8
    @9
    wi
    #
    wi
    axtgbtwnid.1
    axtgbtwnid.2
    @5
    @26
    @0
    @7
    wcel
    #
    cX
    @0
    wceq
    #
    wi
    vx
    vy
    cX
    cY
    cP
    cP
    @1
    cX
    wceq
    #
    @3
    @27
    @4
    @28
    @29
    @2
    @7
    @0
    @29
    @1
    cX
    @1
    cX
    cI
    @29
    id
    #
    @30
    oveq12d
    eleq2d
    @1
    cX
    @0
    eqeq1
    imbi12d
    @0
    cY
    wceq
    @27
    @8
    @28
    @9
    @0
    cY
    @7
    eleq1
    @0
    cY
    cX
    eqeq2
    imbi12d
    rspc2v
    syl2anc
    mp2d
end
