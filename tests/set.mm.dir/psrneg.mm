include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "eqid.mm"
include "psrlinv.mm"
include "psr0.mm"
include "eqtr4d.mm"
include "cgrp.mm"
include "wcel.mm"
include "wb.mm"
include "psrgrp.mm"
include "psrnegcl.mm"
include "grpinvid2.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem psrneg
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cI: class I
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  assume psrgrp.s: |- S = ( I mPwSer R )
  assume psrgrp.i: |- ( ph -> I e. V )
  assume psrgrp.r: |- ( ph -> R e. Grp )
  assume psrneg.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psrneg.i: |- N = ( invg ` R )
  assume psrneg.b: |- B = ( Base ` S )
  assume psrneg.m: |- M = ( invg ` S )
  assume psrneg.x: |- ( ph -> X e. B )

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
  assert |- ( ph -> ( M ` X ) = ( N o. X ) )

  proof
    wph
    cX
    cM
    cfv
    cN
    cX
    ccom
    #
    wceq
    #
    @0
    cX
    cS
    cplusg
    cfv
    #
    co
    #
    cS
    c0g
    cfv
    #
    wceq
    #
    wph
    @3
    cD
    cR
    c0g
    cfv
    #
    csn
    cxp
    @4
    wph
    cB
    cD
    @2
    cR
    cS
    vf
    cI
    cN
    cV
    cX
    @6
    psrgrp.s
    psrgrp.i
    psrgrp.r
    psrneg.d
    psrneg.i
    psrneg.b
    psrneg.x
    @6
    eqid
    #
    @2
    eqid
    #
    psrlinv
    wph
    cD
    cR
    cS
    vf
    cI
    @6
    cV
    @4
    psrgrp.s
    psrgrp.i
    psrgrp.r
    psrneg.d
    @7
    @4
    eqid
    #
    psr0
    eqtr4d
    wph
    cS
    cgrp
    wcel
    cX
    cB
    wcel
    @0
    cB
    wcel
    @1
    @5
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
    psrneg.x
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    cN
    cV
    cX
    psrgrp.s
    psrgrp.i
    psrgrp.r
    psrneg.d
    psrneg.i
    psrneg.b
    psrneg.x
    psrnegcl
    cB
    @2
    cS
    cM
    cX
    @0
    @4
    psrneg.b
    @8
    @9
    psrneg.m
    grpinvid2
    syl3anc
    mpbird
end
