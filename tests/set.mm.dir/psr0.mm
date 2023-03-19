include "csn.mm"
include "cxp.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "psr0cl.mm"
include "psr0lid.mm"
include "cgrp.mm"
include "wcel.mm"
include "wb.mm"
include "psrgrp.mm"
include "grpid.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem psr0
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cI: class I
  let cO: class O
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
  assume psr0.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psr0.o: |- O = ( 0g ` R )
  assume psr0.z: |- .0. = ( 0g ` S )

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
  assert |- ( ph -> .0. = ( D X. { O } ) )

  proof
    wph
    cD
    cO
    csn
    cxp
    #
    @0
    cS
    cplusg
    cfv
    #
    co
    @0
    wceq
    #
    c.0
    @0
    wceq
    #
    wph
    cS
    cbs
    cfv
    #
    cD
    @1
    cR
    cS
    vf
    cI
    cV
    @0
    cO
    psrgrp.s
    psrgrp.i
    psrgrp.r
    psr0.d
    psr0.o
    @4
    eqid
    #
    @1
    eqid
    #
    wph
    @4
    cD
    cR
    cS
    vf
    cI
    cV
    cO
    psrgrp.s
    psrgrp.i
    psrgrp.r
    psr0.d
    psr0.o
    @5
    psr0cl
    #
    psr0lid
    wph
    cS
    cgrp
    wcel
    @0
    @4
    wcel
    @2
    @3
    wb
    wph
    cR
    cS
    cI
    cV
    psrgrp.s
    psrgrp.i
    psrgrp.r
    psrgrp
    @7
    @4
    @1
    cS
    @0
    c.0
    @5
    @6
    psr0.z
    grpid
    syl2anc
    mpbid
end
