include "cv.mm"
include "cres.mm"
include "wf1o.mm"
include "con0.mm"
include "wrex.mm"
include "crn.mm"
include "wss.mm"
include "dnnumch1.mm"
include "wi.mm"
include "wfo.mm"
include "wceq.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl.mm"
include "resss.mm"
include "rnss.mm"
include "mp1i.mm"
include "eqsstr3d.mm"
include "a1i.mm"
include "rexlimdvw.mm"
include "mpd.mm"

theorem dnnumch2
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  assume dnnumch.f: |- F = recs ( ( z e. _V |-> ( G ` ( A \ ran z ) ) ) )
  assume dnnumch.a: |- ( ph -> A e. V )
  assume dnnumch.g: |- ( ph -> A. y e. ~P A ( y =/= (/) -> ( G ` y ) e. y ) )

  disjoint F y
  disjoint G y
  disjoint G z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint v z
  disjoint w z
  disjoint x z
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint ph v
  disjoint ph x
  disjoint ph w
  assert |- ( ph -> A C_ ran F )

  proof
    wph
    vx
    cv
    #
    cA
    cF
    @0
    cres
    #
    wf1o
    #
    vx
    con0
    wrex
    cA
    cF
    crn
    #
    wss
    #
    wph
    vx
    vy
    vz
    cA
    cF
    cG
    cV
    dnnumch.f
    dnnumch.a
    dnnumch.g
    dnnumch1
    wph
    @2
    @4
    vx
    con0
    @2
    @4
    wi
    wph
    @2
    cA
    @1
    crn
    #
    @3
    @2
    @0
    cA
    @1
    wfo
    @5
    cA
    wceq
    @0
    cA
    @1
    f1ofo
    @0
    cA
    @1
    forn
    syl
    @1
    cF
    wss
    @5
    @3
    wss
    @2
    cF
    @0
    resss
    @1
    cF
    rnss
    mp1i
    eqsstr3d
    a1i
    rexlimdvw
    mpd
end
