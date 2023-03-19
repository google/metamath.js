include "cgrp.mm"
include "wcel.mm"
include "wf1.mm"
include "cv.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "fveq1.mm"
include "co.mm"
include "simpr.mm"
include "grpidcl.mm"
include "adantr.mm"
include "grplactval.mm"
include "syl2anc.mm"
include "grprid.mm"
include "eqtrd.mm"
include "cid.mm"
include "cres.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "symgid.mm"
include "ax-mp.mm"
include "fveq1i.mm"
include "fvresi.mm"
include "syl.mm"
include "syl5eqr.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "ralrimiva.mm"
include "cghm.mm"
include "wb.mm"
include "cayleylem1.mm"
include "eqid.mm"
include "ghmf1.mm"
include "mpbird.mm"

theorem cayleylem2
  let c.pl: class .+
  let cS: class S
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume cayleylem1.x: |- X = ( Base ` G )
  assume cayleylem1.p: |- .+ = ( +g ` G )
  assume cayleylem1.u: |- .0. = ( 0g ` G )
  assume cayleylem1.h: |- H = ( SymGrp ` X )
  assume cayleylem1.s: |- S = ( Base ` H )
  assume cayleylem1.f: |- F = ( g e. X |-> ( a e. X |-> ( g .+ a ) ) )

  disjoint a g
  disjoint .+ a
  disjoint .+ g
  disjoint G a
  disjoint G g
  disjoint H g
  disjoint X a
  disjoint X g
  disjoint .0. a
  disjoint a x
  disjoint a y
  disjoint g x
  disjoint g y
  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint F x
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint X x
  disjoint X y
  disjoint .0. x
  disjoint S x
  assert |- ( G e. Grp -> F : X -1-1-> S )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cS
    cF
    wf1
    #
    vx
    cv
    #
    cF
    cfv
    #
    cH
    c0g
    cfv
    #
    wceq
    #
    @2
    c.0
    wceq
    #
    wi
    #
    vx
    cX
    wral
    #
    @0
    @7
    vx
    cX
    @5
    c.0
    @3
    cfv
    #
    c.0
    @4
    cfv
    #
    wceq
    @0
    @2
    cX
    wcel
    #
    wa
    #
    @6
    c.0
    @3
    @4
    fveq1
    @12
    @9
    @2
    @10
    c.0
    @12
    @9
    @2
    c.0
    c.pl
    co
    #
    @2
    @12
    @11
    c.0
    cX
    wcel
    #
    @9
    @13
    wceq
    @0
    @11
    simpr
    @0
    @14
    @11
    cX
    cG
    c.0
    cayleylem1.x
    cayleylem1.u
    grpidcl
    adantr
    #
    @2
    c.0
    c.pl
    vg
    cF
    cG
    cX
    va
    cayleylem1.f
    cayleylem1.x
    grplactval
    syl2anc
    cX
    c.pl
    cG
    @2
    c.0
    cayleylem1.x
    cayleylem1.p
    cayleylem1.u
    grprid
    eqtrd
    @12
    @10
    c.0
    cid
    cX
    cres
    #
    cfv
    #
    c.0
    c.0
    @16
    @4
    cX
    cvv
    wcel
    @16
    @4
    wceq
    cX
    cG
    cbs
    cfv
    cvv
    cayleylem1.x
    cG
    cbs
    fvex
    eqeltri
    cX
    cH
    cvv
    cayleylem1.h
    symgid
    ax-mp
    fveq1i
    @12
    @14
    @17
    c.0
    wceq
    @15
    cX
    c.0
    fvresi
    syl
    syl5eqr
    eqeq12d
    syl5ib
    ralrimiva
    @0
    cF
    cG
    cH
    cghm
    co
    wcel
    @1
    @8
    wb
    c.pl
    cS
    vg
    cF
    cG
    cH
    cX
    c.0
    va
    cayleylem1.x
    cayleylem1.p
    cayleylem1.u
    cayleylem1.h
    cayleylem1.s
    cayleylem1.f
    cayleylem1
    vx
    cG
    cH
    @4
    cF
    cX
    cS
    c.0
    cayleylem1.x
    cayleylem1.s
    cayleylem1.u
    @4
    eqid
    ghmf1
    syl
    mpbird
end
