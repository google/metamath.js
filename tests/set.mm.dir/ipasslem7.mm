include "cr.mm"
include "cv.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "cmpt.mm"
include "ccn.mm"
include "wcel.mm"
include "wtru.mm"
include "cc.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "crest.mm"
include "tgioo2.mm"
include "eqtri.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "wss.mm"
include "ax-resscn.mm"
include "cims.mm"
include "cmopn.mm"
include "cnmptid.mm"
include "cxmt.mm"
include "cnv.mm"
include "phnvi.mm"
include "eqid.mm"
include "imsxmet.mm"
include "ax-mp.mm"
include "mopntopon.mm"
include "mp1i.mm"
include "cnmptc.mm"
include "ctx.mm"
include "smcn.mm"
include "cnmpt12f.mm"
include "dipcn.mm"
include "dipcl.mm"
include "mp3an.mm"
include "mulcn.mm"
include "subcn.mm"
include "cnmpt1res.mm"
include "trud.mm"
include "eqeltri.mm"

theorem ipasslem7
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  assume ip1i.1: |- X = ( BaseSet ` U )
  assume ip1i.2: |- G = ( +v ` U )
  assume ip1i.4: |- S = ( .sOLD ` U )
  assume ip1i.7: |- P = ( .iOLD ` U )
  assume ip1i.9: |- U e. CPreHilOLD
  assume ipasslem7.a: |- A e. X
  assume ipasslem7.b: |- B e. X
  assume ipasslem7.f: |- F = ( w e. RR |-> ( ( ( w S A ) P B ) - ( w x. ( A P B ) ) ) )
  assume ipasslem7.j: |- J = ( topGen ` ran (,) )
  assume ipasslem7.k: |- K = ( TopOpen ` CCfld )

  disjoint B w
  disjoint K w
  disjoint P w
  disjoint S w
  disjoint U w
  disjoint X w
  disjoint A w
  disjoint F x
  disjoint w x
  disjoint A x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint N x
  disjoint N y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  assert |- F e. ( J Cn K )

  proof
    cF
    vw
    cr
    vw
    cv
    #
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    @0
    cA
    cB
    cP
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cmpt
    #
    cJ
    cK
    ccn
    co
    #
    ipasslem7.f
    @6
    @7
    wcel
    wtru
    vw
    @5
    cK
    cJ
    cK
    cc
    cr
    cJ
    cioo
    crn
    ctg
    cfv
    cK
    cr
    crest
    co
    ipasslem7.j
    cK
    ipasslem7.k
    tgioo2
    eqtri
    cK
    cc
    ctopon
    cfv
    wcel
    wtru
    cK
    ipasslem7.k
    cnfldtopon
    a1i
    #
    cr
    cc
    wss
    wtru
    ax-resscn
    a1i
    wtru
    vw
    @2
    @4
    cmin
    cK
    cK
    cK
    cK
    cc
    @8
    wtru
    vw
    @1
    cB
    cP
    cK
    cU
    cims
    cfv
    #
    cmopn
    cfv
    #
    @10
    cK
    cc
    @8
    wtru
    vw
    @0
    cA
    cS
    cK
    cK
    @10
    @10
    cc
    @8
    wtru
    vw
    cK
    cc
    @8
    cnmptid
    #
    wtru
    vw
    cA
    cK
    @10
    cc
    cX
    @8
    @9
    cX
    cxmt
    cfv
    wcel
    #
    @10
    cX
    ctopon
    cfv
    wcel
    wtru
    cU
    cnv
    wcel
    #
    @12
    cU
    ip1i.9
    phnvi
    #
    @9
    cU
    cX
    ip1i.1
    @9
    eqid
    #
    imsxmet
    ax-mp
    @9
    @10
    cX
    @10
    eqid
    #
    mopntopon
    mp1i
    #
    cA
    cX
    wcel
    #
    wtru
    ipasslem7.a
    a1i
    cnmptc
    @13
    cS
    cK
    @10
    ctx
    co
    @10
    ccn
    co
    wcel
    wtru
    @14
    @9
    cS
    cU
    @10
    cK
    @15
    @16
    ip1i.4
    ipasslem7.k
    smcn
    mp1i
    cnmpt12f
    wtru
    vw
    cB
    cK
    @10
    cc
    cX
    @8
    @17
    cB
    cX
    wcel
    #
    wtru
    ipasslem7.b
    a1i
    cnmptc
    @13
    cP
    @10
    @10
    ctx
    co
    cK
    ccn
    co
    wcel
    wtru
    @14
    @9
    cP
    cU
    @10
    cK
    ip1i.7
    @15
    @16
    ipasslem7.k
    dipcn
    mp1i
    cnmpt12f
    wtru
    vw
    @0
    @3
    cmul
    cK
    cK
    cK
    cK
    cc
    @8
    @11
    wtru
    vw
    @3
    cK
    cK
    cc
    cc
    @8
    @8
    @3
    cc
    wcel
    #
    wtru
    @13
    @18
    @19
    @20
    @14
    ipasslem7.a
    ipasslem7.b
    cA
    cB
    cP
    cU
    cX
    ip1i.1
    ip1i.7
    dipcl
    mp3an
    a1i
    cnmptc
    cmul
    cK
    cK
    ctx
    co
    cK
    ccn
    co
    #
    wcel
    wtru
    cK
    ipasslem7.k
    mulcn
    a1i
    cnmpt12f
    cmin
    @21
    wcel
    wtru
    cK
    ipasslem7.k
    subcn
    a1i
    cnmpt12f
    cnmpt1res
    trud
    eqeltri
end
