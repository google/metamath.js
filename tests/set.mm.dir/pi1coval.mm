include "cv.mm"
include "cphtpc.mm"
include "cfv.mm"
include "cec.mm"
include "ccom.mm"
include "cvv.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "fvex.mm"
include "ecexg.mm"
include "mp1i.mm"
include "eceq1.mm"
include "wceq.mm"
include "coeq2.mm"
include "eceq1d.mm"
include "cbs.mm"
include "wf.mm"
include "wfun.mm"
include "pi1cof.mm"
include "ffun.mm"
include "syl.mm"
include "fliftval.mm"

theorem pi1coval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vh: setvar h
  let vf: setvar f
  let vz: setvar z
  let vy: setvar y
  assume pi1co.p: |- P = ( J pi1 A )
  assume pi1co.q: |- Q = ( K pi1 B )
  assume pi1co.v: |- V = ( Base ` P )
  assume pi1co.g: |- G = ran ( g e. U. V |-> <. [ g ] ( ~=ph ` J ) , [ ( F o. g ) ] ( ~=ph ` K ) >. )
  assume pi1co.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1co.f: |- ( ph -> F e. ( J Cn K ) )
  assume pi1co.a: |- ( ph -> A e. X )
  assume pi1co.b: |- ( ph -> ( F ` A ) = B )

  disjoint A g
  disjoint F g
  disjoint J g
  disjoint g ph
  disjoint K g
  disjoint P g
  disjoint T g
  disjoint Q g
  disjoint V g
  disjoint g s
  disjoint A s
  disjoint g h
  disjoint h s
  disjoint F h
  disjoint F s
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f z
  disjoint J f
  disjoint g z
  disjoint h z
  disjoint J h
  disjoint s z
  disjoint J s
  disjoint J z
  disjoint f y
  disjoint f ph
  disjoint g y
  disjoint h y
  disjoint h ph
  disjoint s y
  disjoint ph s
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint G f
  disjoint G h
  disjoint G y
  disjoint G z
  disjoint K h
  disjoint K s
  disjoint P f
  disjoint P h
  disjoint P s
  disjoint P y
  disjoint P z
  disjoint T s
  disjoint Q f
  disjoint Q h
  disjoint Q s
  disjoint Q y
  disjoint Q z
  disjoint V f
  disjoint V h
  disjoint V s
  disjoint V y
  disjoint V z
  assert |- ( ( ph /\ T e. U. V ) -> ( G ` [ T ] ( ~=ph ` J ) ) = [ ( F o. T ) ] ( ~=ph ` K ) )

  proof
    wph
    vg
    vg
    cv
    #
    cJ
    cphtpc
    cfv
    #
    cec
    #
    cF
    @0
    ccom
    #
    cK
    cphtpc
    cfv
    #
    cec
    #
    cT
    @1
    cec
    cF
    cT
    ccom
    #
    @4
    cec
    cvv
    cvv
    cG
    cV
    cuni
    #
    cT
    pi1co.g
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    wph
    @0
    @7
    wcel
    wa
    #
    cJ
    cphtpc
    fvex
    @0
    cvv
    @1
    ecexg
    mp1i
    @4
    cvv
    wcel
    @5
    cvv
    wcel
    @8
    cK
    cphtpc
    fvex
    @3
    cvv
    @4
    ecexg
    mp1i
    @0
    cT
    @1
    eceq1
    @0
    cT
    wceq
    @3
    @6
    @4
    @0
    cT
    cF
    coeq2
    eceq1d
    wph
    cV
    cQ
    cbs
    cfv
    #
    cG
    wf
    cG
    wfun
    wph
    cA
    cB
    cP
    cQ
    vg
    cF
    cG
    cJ
    cK
    cV
    cX
    pi1co.p
    pi1co.q
    pi1co.v
    pi1co.g
    pi1co.j
    pi1co.f
    pi1co.a
    pi1co.b
    pi1cof
    cV
    @9
    cG
    ffun
    syl
    fliftval
end
