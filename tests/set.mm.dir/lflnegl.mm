include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "clmod.mm"
include "wf.mm"
include "eqid.mm"
include "lflf.mm"
include "syl2anc.mm"
include "c0g.mm"
include "wf1o.mm"
include "crg.mm"
include "cgrp.mm"
include "lmodring.mm"
include "ringgrp.mm"
include "3syl.mm"
include "grpinvf1o.mm"
include "f1of.mm"
include "syl.mm"
include "cv.mm"
include "cmpt.mm"
include "wceq.mm"
include "co.mm"
include "grplinv.mm"
include "sylan.mm"
include "caofinvl.mm"

theorem lflnegl
  let wph: wff ph
  let vx: setvar x
  let c.pl: class .+
  let cR: class R
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vy: setvar y
  let vk: setvar k
  let vz: setvar z
  assume lflnegcl.v: |- V = ( Base ` W )
  assume lflnegcl.r: |- R = ( Scalar ` W )
  assume lflnegcl.i: |- I = ( invg ` R )
  assume lflnegcl.n: |- N = ( x e. V |-> ( I ` ( G ` x ) ) )
  assume lflnegcl.f: |- F = ( LFnl ` W )
  assume lflnegcl.w: |- ( ph -> W e. LMod )
  assume lflnegcl.g: |- ( ph -> G e. F )
  assume lflnegl.p: |- .+ = ( +g ` R )
  assume lflnegl.o: |- .0. = ( 0g ` R )

  disjoint G x
  disjoint I x
  disjoint R x
  disjoint V x
  disjoint W x
  disjoint ph x
  disjoint x y
  disjoint G y
  disjoint I y
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint y z
  disjoint N y
  disjoint N z
  disjoint .0. y
  disjoint .+ y
  disjoint k x
  disjoint R k
  disjoint x z
  disjoint R y
  disjoint R z
  disjoint V y
  disjoint V z
  disjoint W k
  disjoint W y
  disjoint W z
  disjoint k ph
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( N oF .+ G ) = ( V X. { .0. } ) )

  proof
    wph
    vy
    vx
    cV
    c.0
    c.pl
    cR
    cbs
    cfv
    #
    cG
    cN
    cI
    cvv
    cvv
    cV
    cvv
    wcel
    wph
    cV
    cW
    cbs
    cfv
    cvv
    lflnegcl.v
    cW
    cbs
    fvex
    eqeltri
    a1i
    wph
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    cV
    @0
    cG
    wf
    lflnegcl.w
    lflnegcl.g
    cR
    cF
    cG
    @0
    cV
    cW
    clmod
    lflnegcl.r
    @0
    eqid
    #
    lflnegcl.v
    lflnegcl.f
    lflf
    syl2anc
    c.0
    cvv
    wcel
    wph
    c.0
    cR
    c0g
    cfv
    cvv
    lflnegl.o
    cR
    c0g
    fvex
    eqeltri
    a1i
    wph
    @0
    @0
    cI
    wf1o
    @0
    @0
    cI
    wf
    wph
    @0
    cR
    cI
    @2
    lflnegcl.i
    wph
    @1
    cR
    crg
    wcel
    cR
    cgrp
    wcel
    #
    lflnegcl.w
    cR
    cW
    lflnegcl.r
    lmodring
    cR
    ringgrp
    3syl
    #
    grpinvf1o
    @0
    @0
    cI
    f1of
    syl
    cN
    vx
    cV
    vx
    cv
    cG
    cfv
    cI
    cfv
    cmpt
    wceq
    wph
    lflnegcl.n
    a1i
    wph
    @3
    vy
    cv
    #
    @0
    wcel
    @5
    cI
    cfv
    @5
    c.pl
    co
    c.0
    wceq
    @4
    @0
    c.pl
    cR
    cI
    @5
    c.0
    @2
    lflnegl.p
    lflnegl.o
    lflnegcl.i
    grplinv
    sylan
    caofinvl
end
