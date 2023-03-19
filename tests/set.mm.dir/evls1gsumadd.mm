include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cvv.mm"
include "crg.mm"
include "wcel.mm"
include "ccmn.mm"
include "csubrg.mm"
include "subrgring.mm"
include "syl.mm"
include "ply1ring.mm"
include "ringcmn.mm"
include "3syl.mm"
include "wa.mm"
include "cmnd.mm"
include "ccrg.mm"
include "crngring.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "jctir.mm"
include "pwsring.mm"
include "ringmnd.mm"
include "cn0.mm"
include "nn0ex.mm"
include "a1i.mm"
include "ssexd.mm"
include "crh.mm"
include "cghm.mm"
include "cmhm.mm"
include "evls1rhm.mm"
include "syl2anc.mm"
include "rhmghm.mm"
include "ghmmhm.mm"
include "gsummptmhm.mm"
include "eqcomd.mm"

theorem evls1gsumadd
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cK: class K
  let cN: class N
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  assume evls1gsumadd.q: |- Q = ( S evalSub1 R )
  assume evls1gsumadd.k: |- K = ( Base ` S )
  assume evls1gsumadd.w: |- W = ( Poly1 ` U )
  assume evls1gsumadd.0: |- .0. = ( 0g ` W )
  assume evls1gsumadd.u: |- U = ( S |`s R )
  assume evls1gsumadd.p: |- P = ( S ^s K )
  assume evls1gsumadd.b: |- B = ( Base ` W )
  assume evls1gsumadd.s: |- ( ph -> S e. CRing )
  assume evls1gsumadd.r: |- ( ph -> R e. ( SubRing ` S ) )
  assume evls1gsumadd.y: |- ( ( ph /\ x e. N ) -> Y e. B )
  assume evls1gsumadd.n: |- ( ph -> N C_ NN0 )
  assume evls1gsumadd.f: |- ( ph -> ( x e. N |-> Y ) finSupp .0. )

  disjoint B x
  disjoint N x
  disjoint Q x
  disjoint ph x
  assert |- ( ph -> ( Q ` ( W gsum ( x e. N |-> Y ) ) ) = ( P gsum ( x e. N |-> ( Q ` Y ) ) ) )

  proof
    wph
    cP
    vx
    cN
    cY
    cQ
    cfv
    cmpt
    cgsu
    co
    cW
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
    cW
    cP
    cQ
    cvv
    c.0
    evls1gsumadd.b
    evls1gsumadd.0
    wph
    cU
    crg
    wcel
    #
    cW
    crg
    wcel
    cW
    ccmn
    wcel
    wph
    cR
    cS
    csubrg
    cfv
    wcel
    #
    @0
    evls1gsumadd.r
    cR
    cS
    cU
    evls1gsumadd.u
    subrgring
    syl
    cW
    cU
    evls1gsumadd.w
    ply1ring
    cW
    ringcmn
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
    cP
    cmnd
    wcel
    wph
    @2
    @3
    wph
    cS
    ccrg
    wcel
    #
    @2
    evls1gsumadd.s
    cS
    crngring
    syl
    cK
    cS
    cbs
    cfv
    cvv
    evls1gsumadd.k
    cS
    cbs
    fvex
    eqeltri
    jctir
    cS
    cK
    cvv
    cP
    evls1gsumadd.p
    pwsring
    cP
    ringmnd
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
    evls1gsumadd.n
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
    cW
    cP
    cghm
    co
    wcel
    cQ
    cW
    cP
    cmhm
    co
    wcel
    wph
    @4
    @1
    @5
    evls1gsumadd.s
    evls1gsumadd.r
    cK
    cQ
    cR
    cS
    cP
    cU
    cW
    evls1gsumadd.q
    evls1gsumadd.k
    evls1gsumadd.p
    evls1gsumadd.u
    evls1gsumadd.w
    evls1rhm
    syl2anc
    cW
    cP
    cQ
    rhmghm
    cW
    cP
    cQ
    ghmmhm
    3syl
    evls1gsumadd.y
    evls1gsumadd.f
    gsummptmhm
    eqcomd
end
