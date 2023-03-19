include "ccom.mm"
include "cplusg.mm"
include "cfv.mm"
include "cof.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cvv.mm"
include "cbs.mm"
include "wcel.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "a1i.mm"
include "wa.mm"
include "fvexd.mm"
include "eqid.mm"
include "psrelbas.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "wf1o.mm"
include "wf.mm"
include "grpinvf1o.mm"
include "f1of.mm"
include "syl.mm"
include "fveq2.mm"
include "fmptco.mm"
include "offval2.mm"
include "psrnegcl.mm"
include "psradd.mm"
include "cgrp.mm"
include "wceq.mm"
include "grplinv.mm"
include "syl2an2r.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "syl6reqr.mm"
include "3eqtr4d.mm"

theorem psrlinv
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.pl: class .+
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
  assume psrlinv.o: |- .0. = ( 0g ` R )
  assume psrlinv.p: |- .+ = ( +g ` S )

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
  assert |- ( ph -> ( ( N o. X ) .+ X ) = ( D X. { .0. } ) )

  proof
    wph
    cN
    cX
    ccom
    #
    cX
    cR
    cplusg
    cfv
    #
    cof
    co
    vx
    cD
    vx
    cv
    #
    cX
    cfv
    #
    cN
    cfv
    #
    @3
    @1
    co
    #
    cmpt
    #
    @0
    cX
    c.pl
    co
    cD
    c.0
    csn
    cxp
    #
    wph
    vx
    cD
    @4
    @3
    @1
    @0
    cX
    cvv
    cvv
    cR
    cbs
    cfv
    #
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
    psrnegcl.d
    cn0
    cI
    cmap
    ovex
    rabex2
    a1i
    wph
    @2
    cD
    wcel
    #
    wa
    @3
    cN
    fvexd
    wph
    cD
    @8
    @2
    cX
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @8
    cX
    psrgrp.s
    @8
    eqid
    #
    psrnegcl.d
    psrnegcl.b
    psrnegcl.z
    psrelbas
    #
    ffvelrnda
    #
    wph
    vx
    vy
    cD
    @8
    @3
    vy
    cv
    #
    cN
    cfv
    @4
    cX
    cN
    @12
    wph
    vx
    cD
    @8
    cX
    @11
    feqmptd
    #
    wph
    vy
    @8
    @8
    cN
    wph
    @8
    @8
    cN
    wf1o
    @8
    @8
    cN
    wf
    wph
    @8
    cR
    cN
    @10
    psrnegcl.i
    psrgrp.r
    grpinvf1o
    @8
    @8
    cN
    f1of
    syl
    feqmptd
    @13
    @3
    cN
    fveq2
    fmptco
    @14
    offval2
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
    psrnegcl.b
    @1
    eqid
    #
    psrlinv.p
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
    psrnegcl.d
    psrnegcl.i
    psrnegcl.b
    psrnegcl.z
    psrnegcl
    psrnegcl.z
    psradd
    wph
    @6
    vx
    cD
    c.0
    cmpt
    @7
    wph
    vx
    cD
    @5
    c.0
    wph
    cR
    cgrp
    wcel
    @9
    @3
    @8
    wcel
    @5
    c.0
    wceq
    psrgrp.r
    @12
    @8
    @1
    cR
    cN
    @3
    c.0
    @10
    @15
    psrlinv.o
    psrnegcl.i
    grplinv
    syl2an2r
    mpteq2dva
    vx
    cD
    c.0
    fconstmpt
    syl6reqr
    3eqtr4d
end
