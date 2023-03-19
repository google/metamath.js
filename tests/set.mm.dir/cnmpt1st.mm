include "cv.mm"
include "cmpt2.mm"
include "c1st.mm"
include "cxp.mm"
include "cres.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "cfv.mm"
include "cmpt.mm"
include "wfn.mm"
include "wceq.mm"
include "cvv.mm"
include "wss.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "ax-mp.mm"
include "ssv.mm"
include "fnssres.mm"
include "mp2an.mm"
include "dffn5.mm"
include "mpbi.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "vex.mm"
include "op1std.mm"
include "mpt2mpt.mm"
include "3eqtri.mm"
include "ctopon.mm"
include "wcel.mm"
include "tx1cn.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"

theorem cnmpt1st
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cL: class L
  let cM: class M
  let cN: class N
  let cP: class P
  let cW: class W
  let cZ: class Z
  assume cnmpt21.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt21.k: |- ( ph -> K e. ( TopOn ` Y ) )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint C u
  disjoint C v
  disjoint D w
  disjoint D z
  disjoint J v
  disjoint J z
  disjoint w x
  disjoint w y
  disjoint F w
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint v x
  disjoint v y
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint ph v
  disjoint ph z
  disjoint u x
  disjoint u y
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint M v
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint K v
  disjoint K z
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint Z z
  assert |- ( ph -> ( x e. X , y e. Y |-> x ) e. ( ( J tX K ) Cn J ) )

  proof
    wph
    vx
    vy
    cX
    cY
    vx
    cv
    #
    cmpt2
    #
    c1st
    cX
    cY
    cxp
    #
    cres
    #
    cJ
    cK
    ctx
    co
    cJ
    ccn
    co
    #
    @3
    vz
    @2
    vz
    cv
    #
    @3
    cfv
    #
    cmpt
    #
    vz
    @2
    @5
    c1st
    cfv
    #
    cmpt
    @1
    @3
    @2
    wfn
    #
    @3
    @7
    wceq
    c1st
    cvv
    wfn
    #
    @2
    cvv
    wss
    @9
    cvv
    cvv
    c1st
    wfo
    @10
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    @2
    ssv
    cvv
    @2
    c1st
    fnssres
    mp2an
    vz
    @2
    @3
    dffn5
    mpbi
    vz
    @2
    @6
    @8
    @5
    @2
    c1st
    fvres
    mpteq2ia
    vx
    vy
    vz
    cX
    cY
    @8
    @0
    @0
    vy
    cv
    @5
    vx
    vex
    vy
    vex
    op1std
    mpt2mpt
    3eqtri
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cK
    cY
    ctopon
    cfv
    wcel
    @3
    @4
    wcel
    cnmpt21.j
    cnmpt21.k
    cJ
    cK
    cX
    cY
    tx1cn
    syl2anc
    syl5eqelr
end
