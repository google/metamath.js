include "csn.mm"
include "cxp.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "wcel.mm"
include "cgrp.mm"
include "eqid.mm"
include "grpidcl.mm"
include "fconst6g.mm"
include "3syl.mm"
include "fvex.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "ovex.mm"
include "rabex2.mm"
include "elmap.mm"
include "sylibr.mm"
include "psrbas.mm"
include "eleqtrrd.mm"

theorem psr0cl
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cI: class I
  let cV: class V
  let c.0: class .0.
  let vx: setvar x
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  let cX: class X
  assume psrgrp.s: |- S = ( I mPwSer R )
  assume psrgrp.i: |- ( ph -> I e. V )
  assume psrgrp.r: |- ( ph -> R e. Grp )
  assume psr0cl.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psr0cl.o: |- .0. = ( 0g ` R )
  assume psr0cl.b: |- B = ( Base ` S )

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
  assert |- ( ph -> ( D X. { .0. } ) e. B )

  proof
    wph
    cD
    c.0
    csn
    cxp
    #
    cR
    cbs
    cfv
    #
    cD
    cmap
    co
    #
    cB
    wph
    cD
    @1
    @0
    wf
    #
    @0
    @2
    wcel
    wph
    cR
    cgrp
    wcel
    c.0
    @1
    wcel
    @3
    psrgrp.r
    @1
    cR
    c.0
    @1
    eqid
    #
    psr0cl.o
    grpidcl
    cD
    c.0
    @1
    fconst6g
    3syl
    @1
    cD
    @0
    cR
    cbs
    fvex
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
    elmap
    sylibr
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @1
    cV
    psrgrp.s
    @4
    psr0cl.d
    psr0cl.b
    psrgrp.i
    psrbas
    eleqtrrd
end
