include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "csubg.mm"
include "wf1o.mm"
include "cress.mm"
include "cghm.mm"
include "wrex.mm"
include "eqid.mm"
include "cayley.mm"
include "simp1d.mm"
include "simp2d.mm"
include "simp3d.mm"
include "f1oeq1.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "f1oeq3.mm"
include "rexeqbidv.mm"

theorem cayleyth
  let vf: setvar f
  let cG: class G
  let cH: class H
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vg: setvar g
  let c.pl: class .+
  assume cayley.x: |- X = ( Base ` G )
  assume cayley.h: |- H = ( SymGrp ` X )

  disjoint f s
  disjoint G f
  disjoint G s
  disjoint H f
  disjoint H s
  disjoint X f
  disjoint X s
  disjoint a f
  disjoint a g
  disjoint a s
  disjoint G a
  disjoint f g
  disjoint g s
  disjoint G g
  disjoint H g
  disjoint .+ a
  disjoint .+ g
  disjoint X a
  disjoint X g
  assert |- ( G e. Grp -> E. s e. ( SubGrp ` H ) E. f e. ( G GrpHom ( H |`s s ) ) f : X -1-1-onto-> s )

  proof
    cG
    cgrp
    wcel
    #
    vg
    cX
    va
    cX
    vg
    cv
    va
    cv
    cG
    cplusg
    cfv
    #
    co
    cmpt
    cmpt
    #
    crn
    #
    cH
    csubg
    cfv
    #
    wcel
    #
    cX
    @3
    vf
    cv
    #
    wf1o
    #
    vf
    cG
    cH
    @3
    cress
    co
    #
    cghm
    co
    #
    wrex
    #
    cX
    vs
    cv
    #
    @6
    wf1o
    #
    vf
    cG
    cH
    @11
    cress
    co
    #
    cghm
    co
    #
    wrex
    #
    vs
    @4
    wrex
    @0
    @5
    @2
    @9
    wcel
    #
    cX
    @3
    @2
    wf1o
    #
    @1
    @3
    vg
    @2
    cG
    cH
    cX
    va
    cayley.x
    cayley.h
    @1
    eqid
    @2
    eqid
    @3
    eqid
    cayley
    #
    simp1d
    @0
    @16
    @17
    @10
    @0
    @5
    @16
    @17
    @18
    simp2d
    @0
    @5
    @16
    @17
    @18
    simp3d
    @7
    @17
    vf
    @2
    @9
    cX
    @3
    @6
    @2
    f1oeq1
    rspcev
    syl2anc
    @15
    @10
    vs
    @3
    @4
    @11
    @3
    wceq
    #
    @12
    @7
    vf
    @14
    @9
    @19
    @13
    @8
    cG
    cghm
    @11
    @3
    cH
    cress
    oveq2
    oveq2d
    @11
    @3
    cX
    @6
    f1oeq3
    rexeqbidv
    rspcev
    syl2anc
end
