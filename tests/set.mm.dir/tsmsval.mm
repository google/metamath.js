include "cvv.mm"
include "wf.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fex2.mm"
include "syl3anc.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "tsmsval2.mm"

theorem tsmsval
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cL: class L
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vs: setvar s
  let vw: setvar w
  assume tsmsval.b: |- B = ( Base ` G )
  assume tsmsval.j: |- J = ( TopOpen ` G )
  assume tsmsval.s: |- S = ( ~P A i^i Fin )
  assume tsmsval.l: |- L = ran ( z e. S |-> { y e. S | z C_ y } )
  assume tsmsval.g: |- ( ph -> G e. V )
  assume tsmsval.a: |- ( ph -> A e. W )
  assume tsmsval.f: |- ( ph -> F : A --> B )

  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint G z
  disjoint ph y
  disjoint ph z
  disjoint S y
  disjoint f s
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint s w
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint G f
  disjoint G s
  disjoint G w
  disjoint f ph
  disjoint ph s
  disjoint ph w
  disjoint S f
  disjoint S s
  disjoint S w
  disjoint J f
  disjoint J s
  disjoint J w
  disjoint L f
  disjoint L s
  disjoint L w
  assert |- ( ph -> ( G tsums F ) = ( ( J fLimf ( S filGen L ) ) ` ( y e. S |-> ( G gsum ( F |` y ) ) ) ) )

  proof
    wph
    vy
    vz
    cA
    cB
    cS
    cF
    cG
    cJ
    cL
    cV
    cvv
    tsmsval.b
    tsmsval.j
    tsmsval.s
    tsmsval.l
    tsmsval.g
    wph
    cA
    cB
    cF
    wf
    #
    cA
    cW
    wcel
    cB
    cvv
    wcel
    #
    cF
    cvv
    wcel
    tsmsval.f
    tsmsval.a
    @1
    wph
    cB
    cG
    cbs
    cfv
    cvv
    tsmsval.b
    cG
    cbs
    fvex
    eqeltri
    a1i
    cA
    cB
    cF
    cW
    cvv
    fex2
    syl3anc
    wph
    @0
    cF
    cdm
    cA
    wceq
    tsmsval.f
    cA
    cB
    cF
    fdm
    syl
    tsmsval2
end
