include "csn.mm"
include "cxp.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "cof.mm"
include "eqid.mm"
include "psr0cl.mm"
include "psradd.mm"
include "cbs.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "a1i.mm"
include "psrelbas.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cgrp.mm"
include "wceq.mm"
include "grplid.mm"
include "sylan.mm"
include "caofid0l.mm"
include "eqtrd.mm"

theorem psr0lid
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cI: class I
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  assume psrgrp.s: |- S = ( I mPwSer R )
  assume psrgrp.i: |- ( ph -> I e. V )
  assume psrgrp.r: |- ( ph -> R e. Grp )
  assume psr0cl.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psr0cl.o: |- .0. = ( 0g ` R )
  assume psr0cl.b: |- B = ( Base ` S )
  assume psr0lid.p: |- .+ = ( +g ` S )
  assume psr0lid.x: |- ( ph -> X e. B )

  disjoint I f
  disjoint .0. x
  disjoint r s
  disjoint r t
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint ph r
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint ph s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint ph t
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint R r
  disjoint R s
  disjoint R t
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint D x
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint N x
  disjoint N y
  disjoint X x
  disjoint X y
  assert |- ( ph -> ( ( D X. { .0. } ) .+ X ) = X )

  proof
    wph
    cD
    c.0
    csn
    cxp
    #
    cX
    c.pl
    co
    @0
    cX
    cR
    cplusg
    cfv
    #
    cof
    co
    cX
    wph
    cB
    @1
    c.pl
    cR
    cS
    cI
    @0
    cX
    psrgrp.s
    psr0cl.b
    @1
    eqid
    #
    psr0lid.p
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    cV
    c.0
    psrgrp.s
    psrgrp.i
    psrgrp.r
    psr0cl.d
    psr0cl.o
    psr0cl.b
    psr0cl
    psr0lid.x
    psradd
    wph
    vx
    cD
    c.0
    @1
    cR
    cbs
    cfv
    #
    cX
    cvv
    cvv
    cD
    cvv
    wcel
    wph
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    cD
    psr0cl.d
    cn0
    cI
    cmap
    ovex
    rabex2
    a1i
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @3
    cX
    psrgrp.s
    @3
    eqid
    #
    psr0cl.d
    psr0cl.b
    psr0lid.x
    psrelbas
    c.0
    cvv
    wcel
    wph
    c.0
    cR
    c0g
    cfv
    cvv
    psr0cl.o
    cR
    c0g
    fvex
    eqeltri
    a1i
    wph
    cR
    cgrp
    wcel
    vx
    cv
    #
    @3
    wcel
    c.0
    @5
    @1
    co
    @5
    wceq
    psrgrp.r
    @3
    @1
    cR
    @5
    c.0
    @4
    @2
    psr0cl.o
    grplid
    sylan
    caofid0l
    eqtrd
end
