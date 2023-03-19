include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cint.mm"
include "con0.mm"
include "cmpt.mm"
include "cfv.mm"
include "wceq.mm"
include "simpr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wfn.mm"
include "cvv.mm"
include "crn.mm"
include "cdif.mm"
include "tfr1.mm"
include "fndm.mm"
include "ax-mp.mm"
include "sseqtri.mm"
include "dnnumch2.mm"
include "sselda.mm"
include "inisegn0.mm"
include "sylib.mm"
include "oninton.mm"
include "sylancr.mm"
include "weq.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "inteqd.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem dnnumch3lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vv: setvar v
  assume dnnumch.f: |- F = recs ( ( z e. _V |-> ( G ` ( A \ ran z ) ) ) )
  assume dnnumch.a: |- ( ph -> A e. V )
  assume dnnumch.g: |- ( ph -> A. y e. ~P A ( y =/= (/) -> ( G ` y ) e. y ) )

  disjoint F w
  disjoint F x
  disjoint F y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint ph x
  disjoint ph w
  disjoint F v
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint G v
  disjoint v z
  disjoint A v
  disjoint ph v
  assert |- ( ( ph /\ w e. A ) -> ( ( x e. A |-> |^| ( `' F " { x } ) ) ` w ) = |^| ( `' F " { w } ) )

  proof
    wph
    vw
    cv
    #
    cA
    wcel
    #
    wa
    #
    @1
    cF
    ccnv
    #
    @0
    csn
    #
    cima
    #
    cint
    #
    con0
    wcel
    #
    @0
    vx
    cA
    @3
    vx
    cv
    #
    csn
    #
    cima
    #
    cint
    #
    cmpt
    #
    cfv
    @6
    wceq
    wph
    @1
    simpr
    @2
    @5
    con0
    wss
    @5
    c0
    wne
    #
    @7
    @5
    cF
    cdm
    #
    con0
    cF
    @4
    cnvimass
    cF
    con0
    wfn
    @14
    con0
    wceq
    cF
    vz
    cvv
    cA
    vz
    cv
    crn
    cdif
    cG
    cfv
    cmpt
    dnnumch.f
    tfr1
    con0
    cF
    fndm
    ax-mp
    sseqtri
    @2
    @0
    cF
    crn
    #
    wcel
    @13
    wph
    cA
    @15
    @0
    wph
    vy
    vz
    cA
    cF
    cG
    cV
    dnnumch.f
    dnnumch.a
    dnnumch.g
    dnnumch2
    sselda
    @0
    cF
    inisegn0
    sylib
    @5
    oninton
    sylancr
    vx
    @0
    @11
    @6
    cA
    con0
    @12
    vx
    vw
    weq
    #
    @10
    @5
    @16
    @9
    @4
    @3
    @8
    @0
    sneq
    imaeq2d
    inteqd
    @12
    eqid
    fvmptg
    syl2anc
end
