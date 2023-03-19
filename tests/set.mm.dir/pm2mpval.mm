include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cpm2mp.mm"
include "co.mm"
include "cn0.mm"
include "cv.mm"
include "cdecpmat.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cvv.mm"
include "cpl1.mm"
include "cfv.mm"
include "cmat.mm"
include "cbs.mm"
include "cv1.mm"
include "cmgp.mm"
include "cmg.mm"
include "cvsca.mm"
include "csb.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-pm2mp.mm"
include "a1i.mm"
include "simpl.mm"
include "fveq2.mm"
include "adantl.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "ovex.mm"
include "fvexd.mm"
include "simpr.mm"
include "adantr.mm"
include "eqtrd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "mpteq2dv.mm"
include "csbied.mm"
include "csbie.mm"
include "oveq12.mm"
include "syl5eq.mm"
include "mpteq12dv.mm"
include "elex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "ovmpt2d.mm"

theorem pm2mpval
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let vk: setvar k
  let vm: setvar m
  let c.ex: class .^
  let c.as: class .*
  let cN: class N
  let cV: class V
  let cX: class X
  let vn: setvar n
  let vr: setvar r
  let va: setvar a
  let vq: setvar q
  assume pm2mpval.p: |- P = ( Poly1 ` R )
  assume pm2mpval.c: |- C = ( N Mat P )
  assume pm2mpval.b: |- B = ( Base ` C )
  assume pm2mpval.m: |- .* = ( .s ` Q )
  assume pm2mpval.e: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume pm2mpval.x: |- X = ( var1 ` A )
  assume pm2mpval.a: |- A = ( N Mat R )
  assume pm2mpval.q: |- Q = ( Poly1 ` A )
  assume pm2mpval.t: |- T = ( N pMatToMatPoly R )

  disjoint B m
  disjoint N k
  disjoint N m
  disjoint k m
  disjoint R k
  disjoint R m
  disjoint V m
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint N n
  disjoint N r
  disjoint k n
  disjoint k r
  disjoint Q n
  disjoint Q r
  disjoint R n
  disjoint R r
  disjoint V n
  disjoint V r
  disjoint X n
  disjoint X r
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a q
  disjoint a r
  disjoint k q
  disjoint m q
  disjoint n q
  disjoint q r
  disjoint .* n
  disjoint .* r
  disjoint .^ n
  disjoint .^ r
  assert |- ( ( N e. Fin /\ R e. V ) -> T = ( m e. B |-> ( Q gsum ( k e. NN0 |-> ( ( m decompPMat k ) .* ( k .^ X ) ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    #
    cT
    cN
    cR
    cpm2mp
    co
    vm
    cB
    cQ
    vk
    cn0
    vm
    cv
    vk
    cv
    #
    cdecpmat
    co
    #
    @3
    cX
    c.ex
    co
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    pm2mpval.t
    @2
    vn
    vr
    cN
    cR
    cfn
    cvv
    vm
    vn
    cv
    #
    vr
    cv
    #
    cpl1
    cfv
    #
    cmat
    co
    #
    cbs
    cfv
    #
    va
    @10
    @11
    cmat
    co
    #
    vq
    va
    cv
    #
    cpl1
    cfv
    #
    vq
    cv
    #
    vk
    cn0
    @4
    @3
    @16
    cv1
    cfv
    #
    @18
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    @18
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    csb
    #
    csb
    #
    cmpt
    #
    @9
    cpm2mp
    cvv
    cpm2mp
    vn
    vr
    cfn
    cvv
    @29
    cmpt2
    wceq
    @2
    vk
    vm
    vn
    vr
    vq
    va
    df-pm2mp
    a1i
    @2
    @10
    cN
    wceq
    #
    @11
    cR
    wceq
    #
    wa
    #
    wa
    #
    vm
    @14
    @28
    cB
    @8
    @32
    @14
    cB
    wceq
    @2
    @32
    @14
    cN
    cR
    cpl1
    cfv
    #
    cmat
    co
    #
    cbs
    cfv
    #
    cB
    @32
    @13
    @35
    cbs
    @32
    @10
    cN
    @12
    @34
    cmat
    @30
    @31
    simpl
    @31
    @12
    @34
    wceq
    @30
    @11
    cR
    cpl1
    fveq2
    adantl
    oveq12d
    fveq2d
    cB
    cC
    cbs
    cfv
    #
    @36
    pm2mpval.b
    cC
    @35
    cbs
    cC
    cN
    cP
    cmat
    co
    @35
    pm2mpval.c
    cP
    @34
    cN
    cmat
    pm2mpval.p
    oveq2i
    eqtri
    fveq2i
    eqtri
    syl6eqr
    adantl
    @33
    @28
    @15
    cpl1
    cfv
    #
    vk
    cn0
    @4
    @3
    @15
    cv1
    cfv
    #
    @38
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    @38
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @8
    va
    @15
    @27
    @46
    @10
    @11
    cmat
    ovex
    @16
    @15
    wceq
    #
    vq
    @17
    @26
    @46
    cvv
    @47
    @16
    cpl1
    fvexd
    @47
    @18
    @17
    wceq
    #
    wa
    #
    @18
    @38
    @25
    @45
    cgsu
    @49
    @18
    @17
    @38
    @47
    @48
    simpr
    @47
    @17
    @38
    wceq
    @48
    @16
    @15
    cpl1
    fveq2
    adantr
    eqtrd
    #
    @49
    vk
    cn0
    @24
    @44
    @49
    @4
    @4
    @22
    @42
    @23
    @43
    @49
    @18
    @38
    cvsca
    @50
    fveq2d
    @49
    @4
    eqidd
    @49
    @3
    @3
    @19
    @39
    @21
    @41
    @49
    @20
    @40
    cmg
    @49
    @18
    @38
    cmgp
    @50
    fveq2d
    fveq2d
    @49
    @3
    eqidd
    @47
    @19
    @39
    wceq
    @48
    @16
    @15
    cv1
    fveq2
    adantr
    oveq123d
    oveq123d
    mpteq2dv
    oveq12d
    csbied
    csbie
    @32
    @46
    @8
    wceq
    @2
    @32
    @38
    cQ
    @45
    @7
    cgsu
    @32
    @38
    cN
    cR
    cmat
    co
    #
    cpl1
    cfv
    #
    cQ
    @32
    @15
    @51
    cpl1
    @10
    cN
    @11
    cR
    cmat
    oveq12
    #
    fveq2d
    #
    cQ
    cA
    cpl1
    cfv
    @52
    pm2mpval.q
    cA
    @51
    cpl1
    pm2mpval.a
    fveq2i
    eqtri
    #
    syl6eqr
    @32
    vk
    cn0
    @44
    @6
    @32
    @4
    @4
    @42
    @5
    @43
    c.as
    @32
    @43
    @52
    cvsca
    cfv
    #
    c.as
    @32
    @38
    @52
    cvsca
    @54
    fveq2d
    c.as
    cQ
    cvsca
    cfv
    @56
    pm2mpval.m
    cQ
    @52
    cvsca
    @55
    fveq2i
    eqtri
    syl6eqr
    @32
    @4
    eqidd
    @32
    @3
    @3
    @39
    cX
    @41
    c.ex
    @32
    @41
    @52
    cmgp
    cfv
    #
    cmg
    cfv
    #
    c.ex
    @32
    @40
    @57
    cmg
    @32
    @38
    @52
    cmgp
    @54
    fveq2d
    fveq2d
    c.ex
    cQ
    cmgp
    cfv
    #
    cmg
    cfv
    @58
    pm2mpval.e
    @59
    @57
    cmg
    cQ
    @52
    cmgp
    @55
    fveq2i
    fveq2i
    eqtri
    syl6eqr
    @32
    @3
    eqidd
    @32
    @39
    @51
    cv1
    cfv
    #
    cX
    @32
    @15
    @51
    cv1
    @53
    fveq2d
    cX
    cA
    cv1
    cfv
    @60
    pm2mpval.x
    cA
    @51
    cv1
    pm2mpval.a
    fveq2i
    eqtri
    syl6eqr
    oveq123d
    oveq123d
    mpteq2dv
    oveq12d
    adantl
    syl5eq
    mpteq12dv
    @0
    @1
    simpl
    @1
    cR
    cvv
    wcel
    @0
    cR
    cV
    elex
    adantl
    @9
    cvv
    wcel
    @2
    vm
    cB
    @8
    cB
    @37
    cvv
    pm2mpval.b
    cC
    cbs
    fvex
    eqeltri
    mptex
    a1i
    ovmpt2d
    syl5eq
end
