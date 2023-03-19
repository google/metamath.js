include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cvv.mm"
include "wa.mm"
include "cmps.mm"
include "reldmpsr.mm"
include "elbasov.mm"
include "syl.mm"
include "simpld.mm"
include "psrbas.mm"
include "eleqtrd.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "ovex.mm"
include "rabex2.mm"
include "elmap.mm"
include "sylib.mm"

theorem psrelbas
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cI: class I
  let cK: class K
  let cX: class X
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  assume psrbas.s: |- S = ( I mPwSer R )
  assume psrbas.k: |- K = ( Base ` R )
  assume psrbas.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psrbas.b: |- B = ( Base ` S )
  assume psrelbas.x: |- ( ph -> X e. B )

  disjoint I f
  disjoint g h
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint D g
  disjoint h k
  disjoint h x
  disjoint h y
  disjoint D h
  disjoint k x
  disjoint k y
  disjoint D k
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint I g
  disjoint I h
  disjoint I k
  disjoint I x
  disjoint I y
  disjoint K g
  disjoint K h
  disjoint K k
  disjoint K x
  disjoint g ph
  disjoint h ph
  disjoint k ph
  disjoint ph x
  disjoint R g
  disjoint R h
  disjoint R k
  disjoint R x
  disjoint V x
  assert |- ( ph -> X : D --> K )

  proof
    wph
    cX
    cK
    cD
    cmap
    co
    #
    wcel
    cD
    cK
    cX
    wf
    wph
    cX
    cB
    @0
    psrelbas.x
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    cK
    cvv
    psrbas.s
    psrbas.k
    psrbas.d
    psrbas.b
    wph
    cI
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    wph
    cX
    cB
    wcel
    @1
    @2
    wa
    psrelbas.x
    cX
    cB
    cS
    cmps
    cI
    cR
    reldmpsr
    psrbas.s
    psrbas.b
    elbasov
    syl
    simpld
    psrbas
    eleqtrd
    cK
    cD
    cX
    cK
    cR
    cbs
    cfv
    cvv
    psrbas.k
    cR
    cbs
    fvex
    eqeltri
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
    psrbas.d
    cn0
    cI
    cmap
    ovex
    rabex2
    elmap
    sylib
end
