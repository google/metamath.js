include "cfusgr.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "clwlksf1clwwlk.mm"
include "clwlksfoclwwlk.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem clwlksf1oclwwlk
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cN: class N
  let vc: setvar c
  let vi: setvar i
  let cW: class W
  let vx: setvar x
  let vf: setvar f
  let vw: setvar w
  let vy: setvar y
  let cU: class U
  let vu: setvar u
  assume clwlksfclwwlk.1: |- A = ( 1st ` c )
  assume clwlksfclwwlk.2: |- B = ( 2nd ` c )
  assume clwlksfclwwlk.c: |- C = { c e. ( ClWalks ` G ) | ( # ` A ) = N }
  assume clwlksfclwwlk.f: |- F = ( c e. C |-> ( B substr <. 0 , ( # ` A ) >. ) )

  disjoint G c
  disjoint N c
  disjoint C c
  disjoint F c
  disjoint A i
  disjoint B i
  disjoint G i
  disjoint c i
  disjoint W c
  disjoint C i
  disjoint G x
  disjoint i x
  disjoint N i
  disjoint C f
  disjoint C w
  disjoint f w
  disjoint F f
  disjoint F w
  disjoint c f
  disjoint c w
  disjoint G f
  disjoint G w
  disjoint N f
  disjoint N w
  disjoint W i
  disjoint G y
  disjoint N y
  disjoint U c
  disjoint U y
  disjoint c y
  disjoint W y
  disjoint i u
  disjoint i w
  disjoint u w
  disjoint C u
  disjoint F u
  disjoint G u
  disjoint c u
  disjoint N u
  assert |- ( ( G e. FinUSGraph /\ N e. Prime ) -> F : C -1-1-onto-> ( N ClWWalksN G ) )

  proof
    cG
    cfusgr
    wcel
    cN
    cprime
    wcel
    wa
    cC
    cN
    cG
    cclwwlkn
    co
    #
    cF
    wf1
    cC
    @0
    cF
    wfo
    cC
    @0
    cF
    wf1o
    cA
    cB
    cC
    cF
    cG
    cN
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksf1clwwlk
    cA
    cB
    cC
    cF
    cG
    cN
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksfoclwwlk
    cC
    @0
    cF
    df-f1o
    sylanbrc
end
