include "ccom.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "wcel.mm"
include "wf1o.mm"
include "eqid.mm"
include "grpinvf1o.mm"
include "f1of.mm"
include "syl.mm"
include "psrelbas.mm"
include "fco.mm"
include "syl2anc.mm"
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

theorem psrnegcl
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cI: class I
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
  assume psrnegcl.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psrnegcl.i: |- N = ( invg ` R )
  assume psrnegcl.b: |- B = ( Base ` S )
  assume psrnegcl.z: |- ( ph -> X e. B )

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
  assert |- ( ph -> ( N o. X ) e. B )

  proof
    wph
    cN
    cX
    ccom
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
    @1
    @1
    cN
    wf
    #
    cD
    @1
    cX
    wf
    @3
    wph
    @1
    @1
    cN
    wf1o
    @4
    wph
    @1
    cR
    cN
    @1
    eqid
    #
    psrnegcl.i
    psrgrp.r
    grpinvf1o
    @1
    @1
    cN
    f1of
    syl
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @1
    cX
    psrgrp.s
    @5
    psrnegcl.d
    psrnegcl.b
    psrnegcl.z
    psrelbas
    cD
    @1
    @1
    cN
    cX
    fco
    syl2anc
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
    psrnegcl.d
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
    @5
    psrnegcl.d
    psrnegcl.b
    psrgrp.i
    psrbas
    eleqtrrd
end
