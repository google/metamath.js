include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cminusg.mm"
include "wceq.mm"
include "eqid.mm"
include "grplactcnv.mm"
include "simpld.mm"

theorem grplactf1o
  let cA: class A
  let c.pl: class .+
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let cI: class I
  let cB: class B
  assume grplact.1: |- F = ( g e. X |-> ( a e. X |-> ( g .+ a ) ) )
  assume grplact.2: |- X = ( Base ` G )
  assume grplact.3: |- .+ = ( +g ` G )

  disjoint a g
  disjoint A a
  disjoint A g
  disjoint G a
  disjoint G g
  disjoint .+ a
  disjoint .+ g
  disjoint X a
  disjoint X g
  disjoint a b
  disjoint b g
  disjoint A b
  disjoint G b
  disjoint I a
  disjoint I b
  disjoint I g
  disjoint .+ b
  disjoint X b
  disjoint B a
  assert |- ( ( G e. Grp /\ A e. X ) -> ( F ` A ) : X -1-1-onto-> X )

  proof
    cG
    cgrp
    wcel
    cA
    cX
    wcel
    wa
    cX
    cX
    cA
    cF
    cfv
    #
    wf1o
    @0
    ccnv
    cA
    cG
    cminusg
    cfv
    #
    cfv
    cF
    cfv
    wceq
    cA
    c.pl
    vg
    cF
    cG
    @1
    cX
    va
    grplact.1
    grplact.2
    grplact.3
    @1
    eqid
    grplactcnv
    simpld
end
