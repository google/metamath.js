include "ctgp.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "ccnv.mm"
include "chmeo.mm"
include "ctmd.mm"
include "tgptmd.mm"
include "tmdlactcn.mm"
include "sylan.mm"
include "cminusg.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "wf1o.mm"
include "wceq.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "eqid.mm"
include "grplactcnv.mm"
include "simprd.mm"
include "grplactfval.mm"
include "adantl.mm"
include "syl6eqr.mm"
include "cnveqd.mm"
include "grpinvcl.mm"
include "syl.mm"
include "3eqtr3d.mm"
include "syldan.mm"
include "eqeltrd.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem tgplacthmeo
  let vx: setvar x
  let cA: class A
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let vg: setvar g
  assume tgplacthmeo.1: |- F = ( x e. X |-> ( A .+ x ) )
  assume tgplacthmeo.2: |- X = ( Base ` G )
  assume tgplacthmeo.3: |- .+ = ( +g ` G )
  assume tgplacthmeo.4: |- J = ( TopOpen ` G )

  disjoint A x
  disjoint G x
  disjoint J x
  disjoint .+ x
  disjoint X x
  disjoint g x
  disjoint A g
  disjoint G g
  disjoint .+ g
  disjoint X g
  assert |- ( ( G e. TopGrp /\ A e. X ) -> F e. ( J Homeo J ) )

  proof
    cG
    ctgp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cF
    cJ
    cJ
    ccn
    co
    #
    wcel
    #
    cF
    ccnv
    #
    @3
    wcel
    cF
    cJ
    cJ
    chmeo
    co
    wcel
    @0
    cG
    ctmd
    wcel
    #
    @1
    @4
    cG
    tgptmd
    #
    vx
    cA
    c.pl
    cF
    cG
    cJ
    cX
    tgplacthmeo.1
    tgplacthmeo.2
    tgplacthmeo.3
    tgplacthmeo.4
    tmdlactcn
    sylan
    @2
    @5
    vx
    cX
    cA
    cG
    cminusg
    cfv
    #
    cfv
    #
    vx
    cv
    #
    c.pl
    co
    cmpt
    #
    @3
    @2
    cA
    vg
    cX
    vx
    cX
    vg
    cv
    @10
    c.pl
    co
    cmpt
    cmpt
    #
    cfv
    #
    ccnv
    #
    @9
    @12
    cfv
    #
    @5
    @11
    @2
    cX
    cX
    @13
    wf1o
    #
    @14
    @15
    wceq
    #
    @0
    cG
    cgrp
    wcel
    #
    @1
    @16
    @17
    wa
    cG
    tgpgrp
    #
    cA
    c.pl
    vg
    @12
    cG
    @8
    cX
    vx
    @12
    eqid
    #
    tgplacthmeo.2
    tgplacthmeo.3
    @8
    eqid
    #
    grplactcnv
    sylan
    simprd
    @2
    @13
    cF
    @2
    @13
    vx
    cX
    cA
    @10
    c.pl
    co
    cmpt
    #
    cF
    @1
    @13
    @22
    wceq
    @0
    cA
    c.pl
    vg
    @12
    cG
    cX
    vx
    @20
    tgplacthmeo.2
    grplactfval
    adantl
    tgplacthmeo.1
    syl6eqr
    cnveqd
    @2
    @9
    cX
    wcel
    #
    @15
    @11
    wceq
    @0
    @18
    @1
    @23
    @19
    cX
    cG
    @8
    cA
    tgplacthmeo.2
    @21
    grpinvcl
    sylan
    #
    @9
    c.pl
    vg
    @12
    cG
    cX
    vx
    @20
    tgplacthmeo.2
    grplactfval
    syl
    3eqtr3d
    @0
    @1
    @23
    @11
    @3
    wcel
    #
    @24
    @0
    @6
    @23
    @25
    @7
    vx
    @9
    c.pl
    @11
    cG
    cJ
    cX
    @11
    eqid
    tgplacthmeo.2
    tgplacthmeo.3
    tgplacthmeo.4
    tmdlactcn
    sylan
    syldan
    eqeltrd
    cF
    cJ
    cJ
    ishmeo
    sylanbrc
end
