include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "cgim.mm"
include "pi1xfr.mm"
include "cbs.mm"
include "cfv.mm"
include "cuni.mm"
include "cv.mm"
include "cphtpc.mm"
include "cec.mm"
include "cpco.mm"
include "cop.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "pi1xfrcnv.mm"
include "simprd.mm"
include "isgim2.mm"
include "sylanbrc.mm"

theorem pi1xfrgim
  let wph: wff ph
  let vx: setvar x
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
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cH: class H
  assume pi1xfr.p: |- P = ( J pi1 ( F ` 0 ) )
  assume pi1xfr.q: |- Q = ( J pi1 ( F ` 1 ) )
  assume pi1xfr.b: |- B = ( Base ` P )
  assume pi1xfr.g: |- G = ran ( g e. U. B |-> <. [ g ] ( ~=ph ` J ) , [ ( I ( *p ` J ) ( g ( *p ` J ) F ) ) ] ( ~=ph ` J ) >. )
  assume pi1xfr.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1xfr.f: |- ( ph -> F e. ( II Cn J ) )
  assume pi1xfr.i: |- I = ( x e. ( 0 [,] 1 ) |-> ( F ` ( 1 - x ) ) )

  disjoint g x
  disjoint B g
  disjoint B x
  disjoint F g
  disjoint F x
  disjoint I g
  disjoint I x
  disjoint g ph
  disjoint ph x
  disjoint J g
  disjoint J x
  disjoint P g
  disjoint P x
  disjoint Q g
  disjoint Q x
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
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F h
  disjoint F s
  disjoint F u
  disjoint F y
  disjoint F z
  disjoint I h
  disjoint I s
  disjoint I u
  disjoint I y
  disjoint I z
  disjoint A g
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
  disjoint ph y
  disjoint ph z
  disjoint J f
  disjoint J h
  disjoint J s
  disjoint J u
  disjoint J y
  disjoint J z
  disjoint P f
  disjoint P h
  disjoint P s
  disjoint P y
  disjoint P z
  disjoint Q f
  disjoint Q h
  disjoint Q s
  disjoint Q y
  disjoint Q z
  assert |- ( ph -> G e. ( P GrpIso Q ) )

  proof
    wph
    cG
    cP
    cQ
    cghm
    co
    wcel
    cG
    ccnv
    #
    cQ
    cP
    cghm
    co
    wcel
    #
    cG
    cP
    cQ
    cgim
    co
    wcel
    wph
    vx
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
    pi1xfr.i
    pi1xfr
    wph
    @0
    vy
    cQ
    cbs
    cfv
    cuni
    vy
    cv
    #
    cJ
    cphtpc
    cfv
    #
    cec
    cF
    @2
    cI
    cJ
    cpco
    cfv
    #
    co
    @4
    co
    @3
    cec
    cop
    cmpt
    crn
    #
    wceq
    @1
    wph
    vx
    cB
    cP
    cQ
    vg
    vy
    cF
    cG
    @5
    cI
    cJ
    cX
    pi1xfr.p
    pi1xfr.q
    pi1xfr.b
    pi1xfr.g
    pi1xfr.j
    pi1xfr.f
    pi1xfr.i
    @5
    eqid
    pi1xfrcnv
    simprd
    cP
    cQ
    cG
    isgim2
    sylanbrc
end
