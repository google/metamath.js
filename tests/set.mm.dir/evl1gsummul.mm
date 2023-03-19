include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cvv.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "ccrg.mm"
include "wcel.mm"
include "ccmn.mm"
include "ply1crng.mm"
include "crngmgp.mm"
include "3syl.mm"
include "crg.mm"
include "wa.mm"
include "cmnd.mm"
include "crngring.mm"
include "syl.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "jctir.mm"
include "pwsring.mm"
include "ringmgp.mm"
include "cn0.mm"
include "nn0ex.mm"
include "a1i.mm"
include "ssexd.mm"
include "crh.mm"
include "cmhm.mm"
include "evl1rhm.mm"
include "rhmmhm.mm"
include "gsummptmhm.mm"
include "eqcomd.mm"

theorem evl1gsummul
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.1: class .1.
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cW: class W
  let cY: class Y
  assume evl1gsumadd.q: |- Q = ( eval1 ` R )
  assume evl1gsumadd.k: |- K = ( Base ` R )
  assume evl1gsumadd.w: |- W = ( Poly1 ` R )
  assume evl1gsumadd.p: |- P = ( R ^s K )
  assume evl1gsumadd.b: |- B = ( Base ` W )
  assume evl1gsumadd.r: |- ( ph -> R e. CRing )
  assume evl1gsumadd.y: |- ( ( ph /\ x e. N ) -> Y e. B )
  assume evl1gsumadd.n: |- ( ph -> N C_ NN0 )
  assume evl1gsummul.1: |- .1. = ( 1r ` W )
  assume evl1gsummul.g: |- G = ( mulGrp ` W )
  assume evl1gsummul.h: |- H = ( mulGrp ` P )
  assume evl1gsummul.f: |- ( ph -> ( x e. N |-> Y ) finSupp .1. )

  disjoint B x
  disjoint K x
  disjoint N x
  disjoint Q x
  disjoint R x
  disjoint ph x
  assert |- ( ph -> ( Q ` ( G gsum ( x e. N |-> Y ) ) ) = ( H gsum ( x e. N |-> ( Q ` Y ) ) ) )

  proof
    wph
    cH
    vx
    cN
    cY
    cQ
    cfv
    cmpt
    cgsu
    co
    cG
    vx
    cN
    cY
    cmpt
    cgsu
    co
    cQ
    cfv
    wph
    vx
    cN
    cB
    cY
    cG
    cH
    cQ
    cvv
    c.1
    cB
    cW
    cG
    evl1gsummul.g
    evl1gsumadd.b
    mgpbas
    cW
    c.1
    cG
    evl1gsummul.g
    evl1gsummul.1
    ringidval
    wph
    cR
    ccrg
    wcel
    #
    cW
    ccrg
    wcel
    cG
    ccmn
    wcel
    evl1gsumadd.r
    cW
    cR
    evl1gsumadd.w
    ply1crng
    cW
    cG
    evl1gsummul.g
    crngmgp
    3syl
    wph
    cR
    crg
    wcel
    #
    cK
    cvv
    wcel
    #
    wa
    cP
    crg
    wcel
    cH
    cmnd
    wcel
    wph
    @1
    @2
    wph
    @0
    @1
    evl1gsumadd.r
    cR
    crngring
    syl
    cK
    cR
    cbs
    cfv
    cvv
    evl1gsumadd.k
    cR
    cbs
    fvex
    eqeltri
    jctir
    cR
    cK
    cvv
    cP
    evl1gsumadd.p
    pwsring
    cP
    cH
    evl1gsummul.h
    ringmgp
    3syl
    wph
    cN
    cn0
    cvv
    cn0
    cvv
    wcel
    wph
    nn0ex
    a1i
    evl1gsumadd.n
    ssexd
    wph
    @0
    cQ
    cW
    cP
    crh
    co
    wcel
    cQ
    cG
    cH
    cmhm
    co
    wcel
    evl1gsumadd.r
    cK
    cW
    cR
    cP
    cQ
    evl1gsumadd.q
    evl1gsumadd.w
    evl1gsumadd.p
    evl1gsumadd.k
    evl1rhm
    cW
    cP
    cQ
    cG
    cH
    evl1gsummul.g
    evl1gsummul.h
    rhmmhm
    3syl
    evl1gsumadd.y
    evl1gsummul.f
    gsummptmhm
    eqcomd
end
