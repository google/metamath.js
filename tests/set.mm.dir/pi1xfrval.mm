include "cuni.mm"
include "wcel.mm"
include "cphtpc.mm"
include "cfv.mm"
include "cec.mm"
include "cpco.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cvv.mm"
include "wa.mm"
include "fvex.mm"
include "ecexg.mm"
include "mp1i.mm"
include "eceq1.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eceq1d.mm"
include "cbs.mm"
include "wf.mm"
include "wfun.mm"
include "pi1xfrf.mm"
include "ffun.mm"
include "syl.mm"
include "fliftval.mm"
include "mpdan.mm"

theorem pi1xfrval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vs: setvar s
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  assume pi1xfr.p: |- P = ( J pi1 ( F ` 0 ) )
  assume pi1xfr.q: |- Q = ( J pi1 ( F ` 1 ) )
  assume pi1xfr.b: |- B = ( Base ` P )
  assume pi1xfr.g: |- G = ran ( g e. U. B |-> <. [ g ] ( ~=ph ` J ) , [ ( I ( *p ` J ) ( g ( *p ` J ) F ) ) ] ( ~=ph ` J ) >. )
  assume pi1xfr.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1xfr.f: |- ( ph -> F e. ( II Cn J ) )
  assume pi1xfrval.i: |- ( ph -> I e. ( II Cn J ) )
  assume pi1xfrval.1: |- ( ph -> ( F ` 1 ) = ( I ` 0 ) )
  assume pi1xfrval.2: |- ( ph -> ( I ` 1 ) = ( F ` 0 ) )
  assume pi1xfrval.a: |- ( ph -> A e. U. B )

  disjoint B g
  disjoint F g
  disjoint I g
  disjoint A g
  disjoint g ph
  disjoint J g
  disjoint P g
  disjoint Q g
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g h
  disjoint g s
  disjoint g u
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint h s
  disjoint h u
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F h
  disjoint F s
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint I h
  disjoint I s
  disjoint I u
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint A s
  disjoint A x
  disjoint G f
  disjoint G h
  disjoint G y
  disjoint G z
  disjoint H f
  disjoint H s
  disjoint H z
  disjoint f ph
  disjoint h ph
  disjoint ph s
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint J f
  disjoint J h
  disjoint J s
  disjoint J u
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint P f
  disjoint P h
  disjoint P s
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q f
  disjoint Q h
  disjoint Q s
  disjoint Q x
  disjoint Q y
  disjoint Q z
  assert |- ( ph -> ( G ` [ A ] ( ~=ph ` J ) ) = [ ( I ( *p ` J ) ( A ( *p ` J ) F ) ) ] ( ~=ph ` J ) )

  proof
    wph
    cA
    cB
    cuni
    #
    wcel
    cA
    cJ
    cphtpc
    cfv
    #
    cec
    #
    cG
    cfv
    cI
    cA
    cF
    cJ
    cpco
    cfv
    #
    co
    #
    @3
    co
    #
    @1
    cec
    #
    wceq
    pi1xfrval.a
    wph
    vg
    vg
    cv
    #
    @1
    cec
    #
    cI
    @7
    cF
    @3
    co
    #
    @3
    co
    #
    @1
    cec
    #
    @2
    @6
    cvv
    cvv
    cG
    @0
    cA
    pi1xfr.g
    @1
    cvv
    wcel
    #
    @8
    cvv
    wcel
    wph
    @7
    @0
    wcel
    wa
    #
    cJ
    cphtpc
    fvex
    #
    @7
    cvv
    @1
    ecexg
    mp1i
    @12
    @11
    cvv
    wcel
    @13
    @14
    @10
    cvv
    @1
    ecexg
    mp1i
    @7
    cA
    @1
    eceq1
    @7
    cA
    wceq
    #
    @10
    @5
    @1
    @15
    @9
    @4
    cI
    @3
    @7
    cA
    cF
    @3
    oveq1
    oveq2d
    eceq1d
    wph
    cB
    cQ
    cbs
    cfv
    #
    cG
    wf
    cG
    wfun
    wph
    cB
    cP
    cQ
    vg
    cF
    cG
    cI
    cJ
    cX
    pi1xfr.p
    pi1xfr.q
    pi1xfr.b
    pi1xfr.g
    pi1xfr.j
    pi1xfr.f
    pi1xfrval.i
    pi1xfrval.1
    pi1xfrval.2
    pi1xfrf
    cB
    @16
    cG
    ffun
    syl
    fliftval
    mpdan
end
