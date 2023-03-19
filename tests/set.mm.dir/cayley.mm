include "cgrp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "cghm.mm"
include "wf1o.mm"
include "crn.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "cayleylem1.mm"
include "ghmrn.mm"
include "syl.mm"
include "syl5eqel.mm"
include "wss.mm"
include "wb.mm"
include "eqimss2i.mm"
include "resghm2b.mm"
include "sylancl.mm"
include "mpbid.mm"
include "wf1.mm"
include "cayleylem2.mm"
include "f1f1orn.mm"
include "wceq.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "3jca.mm"

theorem cayley
  let c.pl: class .+
  let cS: class S
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let va: setvar a
  let vf: setvar f
  let vs: setvar s
  assume cayley.x: |- X = ( Base ` G )
  assume cayley.h: |- H = ( SymGrp ` X )
  assume cayley.p: |- .+ = ( +g ` G )
  assume cayley.f: |- F = ( g e. X |-> ( a e. X |-> ( g .+ a ) ) )
  assume cayley.s: |- S = ran F

  disjoint a g
  disjoint G a
  disjoint G g
  disjoint H g
  disjoint .+ a
  disjoint .+ g
  disjoint X a
  disjoint X g
  disjoint a f
  disjoint a s
  disjoint f g
  disjoint f s
  disjoint G f
  disjoint g s
  disjoint G s
  disjoint H f
  disjoint H s
  disjoint X f
  disjoint X s
  assert |- ( G e. Grp -> ( S e. ( SubGrp ` H ) /\ F e. ( G GrpHom ( H |`s S ) ) /\ F : X -1-1-onto-> S ) )

  proof
    cG
    cgrp
    wcel
    #
    cS
    cH
    csubg
    cfv
    #
    wcel
    #
    cF
    cG
    cH
    cS
    cress
    co
    #
    cghm
    co
    wcel
    #
    cX
    cS
    cF
    wf1o
    #
    @0
    cS
    cF
    crn
    #
    @1
    cayley.s
    @0
    cF
    cG
    cH
    cghm
    co
    wcel
    #
    @6
    @1
    wcel
    c.pl
    cH
    cbs
    cfv
    #
    vg
    cF
    cG
    cH
    cX
    cG
    c0g
    cfv
    #
    va
    cayley.x
    cayley.p
    @9
    eqid
    #
    cayley.h
    @8
    eqid
    #
    cayley.f
    cayleylem1
    #
    cG
    cH
    cF
    ghmrn
    syl
    syl5eqel
    #
    @0
    @7
    @4
    @12
    @0
    @2
    @6
    cS
    wss
    @7
    @4
    wb
    @13
    cS
    @6
    cayley.s
    eqimss2i
    cG
    cH
    @3
    cF
    cS
    @3
    eqid
    resghm2b
    sylancl
    mpbid
    @0
    cX
    @6
    cF
    wf1o
    #
    @5
    @0
    cX
    @8
    cF
    wf1
    @14
    c.pl
    @8
    vg
    cF
    cG
    cH
    cX
    @9
    va
    cayley.x
    cayley.p
    @10
    cayley.h
    @11
    cayley.f
    cayleylem2
    cX
    @8
    cF
    f1f1orn
    syl
    cS
    @6
    wceq
    @5
    @14
    wb
    cayley.s
    cS
    @6
    cX
    cF
    f1oeq3
    ax-mp
    sylibr
    3jca
end
