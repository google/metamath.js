include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cpred.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "pm3.2i.mm"
include "wfr1.mm"
include "wfr2.mm"
include "rgen.mm"
include "wfr3g.mm"
include "mp3an12.mm"

theorem wfr3
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
  assume wfr3.1: |- R We A
  assume wfr3.2: |- R Se A
  assume wfr3.3: |- F = wrecs ( R , A , G )

  disjoint A z
  disjoint F z
  disjoint G z
  disjoint H z
  disjoint R z
  assert |- ( ( H Fn A /\ A. z e. A ( H ` z ) = ( G ` ( H |` Pred ( R , A , z ) ) ) ) -> F = H )

  proof
    cA
    cR
    wwe
    #
    cA
    cR
    wse
    #
    wa
    cF
    cA
    wfn
    #
    vz
    cv
    #
    cF
    cfv
    cF
    cA
    cR
    @3
    cpred
    #
    cres
    cG
    cfv
    wceq
    #
    vz
    cA
    wral
    #
    wa
    cH
    cA
    wfn
    @3
    cH
    cfv
    cH
    @4
    cres
    cG
    cfv
    wceq
    vz
    cA
    wral
    wa
    cF
    cH
    wceq
    @0
    @1
    wfr3.1
    wfr3.2
    pm3.2i
    @2
    @6
    cA
    cR
    cF
    cG
    wfr3.1
    wfr3.2
    wfr3.3
    wfr1
    @5
    vz
    cA
    cA
    cR
    cF
    cG
    @3
    wfr3.1
    wfr3.2
    wfr3.3
    wfr2
    rgen
    pm3.2i
    vz
    cA
    cR
    cF
    cH
    cG
    wfr3g
    mp3an12
end
