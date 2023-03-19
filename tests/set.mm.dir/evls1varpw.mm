include "cpws.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "wcel.mm"
include "cn0.mm"
include "cbs.mm"
include "cmg.mm"
include "wceq.mm"
include "ccrg.mm"
include "csubrg.mm"
include "wa.mm"
include "crh.mm"
include "jca.mm"
include "eqid.mm"
include "evls1rhm.mm"
include "rhmmhm.mm"
include "3syl.mm"
include "crg.mm"
include "subrgring.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mhmmulg.mm"
include "syl3anc.mm"

theorem evls1varpw
  let wph: wff ph
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let c.ex: class .^
  let cG: class G
  let cN: class N
  let cW: class W
  let cX: class X
  assume evls1varpw.q: |- Q = ( S evalSub1 R )
  assume evls1varpw.u: |- U = ( S |`s R )
  assume evls1varpw.w: |- W = ( Poly1 ` U )
  assume evls1varpw.g: |- G = ( mulGrp ` W )
  assume evls1varpw.x: |- X = ( var1 ` U )
  assume evls1varpw.b: |- B = ( Base ` S )
  assume evls1varpw.e: |- .^ = ( .g ` G )
  assume evls1varpw.s: |- ( ph -> S e. CRing )
  assume evls1varpw.r: |- ( ph -> R e. ( SubRing ` S ) )
  assume evls1varpw.n: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( Q ` ( N .^ X ) ) = ( N ( .g ` ( mulGrp ` ( S ^s B ) ) ) ( Q ` X ) ) )

  proof
    wph
    cQ
    cG
    cS
    cB
    cpws
    co
    #
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    cN
    cn0
    wcel
    cX
    cW
    cbs
    cfv
    #
    wcel
    #
    cN
    cX
    c.ex
    co
    cQ
    cfv
    cN
    cX
    cQ
    cfv
    @1
    cmg
    cfv
    #
    co
    wceq
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
    wa
    cQ
    cW
    @0
    crh
    co
    wcel
    @2
    wph
    @6
    @7
    evls1varpw.s
    evls1varpw.r
    jca
    cB
    cQ
    cR
    cS
    @0
    cU
    cW
    evls1varpw.q
    evls1varpw.b
    @0
    eqid
    evls1varpw.u
    evls1varpw.w
    evls1rhm
    cW
    @0
    cQ
    cG
    @1
    evls1varpw.g
    @1
    eqid
    rhmmhm
    3syl
    evls1varpw.n
    wph
    @7
    cU
    crg
    wcel
    @4
    evls1varpw.r
    cR
    cS
    cU
    evls1varpw.u
    subrgring
    @3
    cW
    cU
    cX
    evls1varpw.x
    evls1varpw.w
    @3
    eqid
    #
    vr1cl
    3syl
    @3
    c.ex
    @5
    cQ
    cG
    @1
    cN
    cX
    @3
    cW
    cG
    evls1varpw.g
    @8
    mgpbas
    evls1varpw.e
    @5
    eqid
    mhmmulg
    syl3anc
end
