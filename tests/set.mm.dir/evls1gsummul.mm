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
include "csubrg.mm"
include "subrgcrng.mm"
include "syl2anc.mm"
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
include "evls1rhm.mm"
include "rhmmhm.mm"
include "gsummptmhm.mm"
include "eqcomd.mm"

theorem evls1gsummul
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let c.1: class .1.
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cW: class W
  let cY: class Y
  assume evls1gsummul.q: |- Q = ( S evalSub1 R )
  assume evls1gsummul.k: |- K = ( Base ` S )
  assume evls1gsummul.w: |- W = ( Poly1 ` U )
  assume evls1gsummul.g: |- G = ( mulGrp ` W )
  assume evls1gsummul.1: |- .1. = ( 1r ` W )
  assume evls1gsummul.u: |- U = ( S |`s R )
  assume evls1gsummul.p: |- P = ( S ^s K )
  assume evls1gsummul.h: |- H = ( mulGrp ` P )
  assume evls1gsummul.b: |- B = ( Base ` W )
  assume evls1gsummul.s: |- ( ph -> S e. CRing )
  assume evls1gsummul.r: |- ( ph -> R e. ( SubRing ` S ) )
  assume evls1gsummul.y: |- ( ( ph /\ x e. N ) -> Y e. B )
  assume evls1gsummul.n: |- ( ph -> N C_ NN0 )
  assume evls1gsummul.f: |- ( ph -> ( x e. N |-> Y ) finSupp .1. )

  disjoint B x
  disjoint N x
  disjoint Q x
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
    evls1gsummul.g
    evls1gsummul.b
    mgpbas
    cW
    c.1
    cG
    evls1gsummul.g
    evls1gsummul.1
    ringidval
    wph
    cU
    ccrg
    wcel
    #
    cW
    ccrg
    wcel
    cG
    ccmn
    wcel
    wph
    cS
    ccrg
    wcel
    #
    cR
    cS
    csubrg
    cfv
    wcel
    #
    @0
    evls1gsummul.s
    evls1gsummul.r
    cR
    cS
    cU
    evls1gsummul.u
    subrgcrng
    syl2anc
    cW
    cU
    evls1gsummul.w
    ply1crng
    cW
    cG
    evls1gsummul.g
    crngmgp
    3syl
    wph
    cS
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
    @3
    @4
    wph
    @1
    @3
    evls1gsummul.s
    cS
    crngring
    syl
    cK
    cS
    cbs
    cfv
    cvv
    evls1gsummul.k
    cS
    cbs
    fvex
    eqeltri
    jctir
    cS
    cK
    cvv
    cP
    evls1gsummul.p
    pwsring
    cP
    cH
    evls1gsummul.h
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
    evls1gsummul.n
    ssexd
    wph
    cQ
    cW
    cP
    crh
    co
    wcel
    #
    cQ
    cG
    cH
    cmhm
    co
    wcel
    wph
    @1
    @2
    @5
    evls1gsummul.s
    evls1gsummul.r
    cK
    cQ
    cR
    cS
    cP
    cU
    cW
    evls1gsummul.q
    evls1gsummul.k
    evls1gsummul.p
    evls1gsummul.u
    evls1gsummul.w
    evls1rhm
    syl2anc
    cW
    cP
    cQ
    cG
    cH
    evls1gsummul.g
    evls1gsummul.h
    rhmmhm
    syl
    evls1gsummul.y
    evls1gsummul.f
    gsummptmhm
    eqcomd
end
