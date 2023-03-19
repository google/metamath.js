include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wceq.mm"
include "matbas2.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"
include "mvmumamul1.mm"

theorem mavmumamul1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vi: setvar i
  let vj: setvar j
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume mavmumamul1.a: |- A = ( N Mat R )
  assume mavmumamul1.m: |- .X. = ( R maMul <. N , N , { (/) } >. )
  assume mavmumamul1.t: |- .x. = ( R maVecMul <. N , N >. )
  assume mavmumamul1.b: |- B = ( Base ` R )
  assume mavmumamul1.r: |- ( ph -> R e. Ring )
  assume mavmumamul1.n: |- ( ph -> N e. Fin )
  assume mavmumamul1.x: |- ( ph -> X e. ( Base ` A ) )
  assume mavmumamul1.y: |- ( ph -> Y e. ( B ^m N ) )
  assume mavmumamul1.z: |- ( ph -> Z e. ( B ^m ( N X. { (/) } ) ) )

  disjoint i j
  disjoint N i
  disjoint N j
  disjoint Y i
  disjoint Y j
  disjoint Z i
  disjoint Z j
  disjoint i ph
  disjoint j ph
  assert |- ( ph -> ( A. j e. N ( Y ` j ) = ( j Z (/) ) -> A. i e. N ( ( X .x. Y ) ` i ) = ( i ( X .X. Z ) (/) ) ) )

  proof
    wph
    cX
    cB
    cR
    c.x
    c.xp
    vi
    vj
    cN
    cN
    cY
    cZ
    mavmumamul1.m
    mavmumamul1.t
    mavmumamul1.b
    mavmumamul1.r
    mavmumamul1.n
    mavmumamul1.n
    wph
    cX
    cA
    cbs
    cfv
    #
    cB
    cN
    cN
    cxp
    cmap
    co
    #
    mavmumamul1.x
    wph
    cN
    cfn
    wcel
    cR
    crg
    wcel
    @1
    @0
    wceq
    mavmumamul1.n
    mavmumamul1.r
    cA
    cR
    cB
    cN
    crg
    mavmumamul1.a
    mavmumamul1.b
    matbas2
    syl2anc
    eleqtrrd
    mavmumamul1.y
    mavmumamul1.z
    mvmumamul1
end
