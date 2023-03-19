include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "wcel.mm"
include "citg2.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cxr.mm"
include "itg2cl.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "itg2ge0.mm"
include "simp3.mm"
include "xrrege0.mm"
include "syl22anc.mm"

theorem itg2lecl
  let cA: class A
  let cF: class F
  let vg: setvar g
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let vh: setvar h
  let vy: setvar y
  let cG: class G


  assert |- ( ( F : RR --> ( 0 [,] +oo ) /\ A e. RR /\ ( S.2 ` F ) <_ A ) -> ( S.2 ` F ) e. RR )

  proof
    cr
    cc0
    cpnf
    cicc
    co
    cF
    wf
    #
    cA
    cr
    wcel
    #
    cF
    citg2
    cfv
    #
    cA
    cle
    wbr
    #
    w3a
    @2
    cxr
    wcel
    #
    @1
    cc0
    @2
    cle
    wbr
    #
    @3
    @2
    cr
    wcel
    @0
    @1
    @4
    @3
    cF
    itg2cl
    3ad2ant1
    @0
    @1
    @3
    simp2
    @0
    @1
    @5
    @3
    cF
    itg2ge0
    3ad2ant1
    @0
    @1
    @3
    simp3
    @2
    cA
    xrrege0
    syl22anc
end
