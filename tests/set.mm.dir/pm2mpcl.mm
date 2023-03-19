include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "pm2mpfval.mm"
include "cvv.mm"
include "c0g.mm"
include "eqid.mm"
include "ccmn.mm"
include "wa.mm"
include "matring.mm"
include "ply1ring.mm"
include "ringcmn.mm"
include "3syl.mm"
include "3adant3.mm"
include "nn0ex.mm"
include "a1i.mm"
include "cbs.mm"
include "adantr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "decpmatcl.mm"
include "syl3anc.mm"
include "cmgp.mm"
include "ply1tmcl.mm"
include "fmptd.mm"
include "csca.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "syl.mm"
include "eqidd.mm"
include "ply1moncl.mm"
include "sylan.mm"
include "cfsupp.mm"
include "wbr.mm"
include "decpmatfsupp.mm"
include "3adant1.mm"
include "wceq.mm"
include "ply1sca.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "breqtrrd.mm"
include "mptscmfsupp0.mm"
include "gsumcl.mm"
include "eqeltrd.mm"

theorem pm2mpcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let c.ex: class .^
  let c.as: class .*
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vb: setvar b
  let vm: setvar m
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vr: setvar r
  let cV: class V
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
  assume pm2mpcl.l: |- L = ( Base ` Q )


  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> ( T ` M ) e. L )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cM
    cT
    cfv
    cQ
    vk
    cn0
    cM
    vk
    cv
    #
    cdecpmat
    co
    #
    @4
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
    cL
    cA
    cB
    cC
    cP
    cQ
    cR
    cT
    vk
    c.ex
    c.as
    cM
    cN
    crg
    cX
    pm2mpval.p
    pm2mpval.c
    pm2mpval.b
    pm2mpval.m
    pm2mpval.e
    pm2mpval.x
    pm2mpval.a
    pm2mpval.q
    pm2mpval.t
    pm2mpfval
    @3
    cn0
    cL
    @8
    cQ
    cvv
    cQ
    c0g
    cfv
    #
    pm2mpcl.l
    @9
    eqid
    #
    @0
    @1
    cQ
    ccmn
    wcel
    #
    @2
    @0
    @1
    wa
    cA
    crg
    wcel
    #
    cQ
    crg
    wcel
    @11
    cA
    cR
    cN
    pm2mpval.a
    matring
    #
    cQ
    cA
    pm2mpval.q
    ply1ring
    cQ
    ringcmn
    3syl
    3adant3
    cn0
    cvv
    wcel
    @3
    nn0ex
    a1i
    #
    @3
    vk
    cn0
    @7
    cL
    @8
    @3
    @4
    cn0
    wcel
    #
    wa
    #
    @12
    @5
    cA
    cbs
    cfv
    #
    wcel
    #
    @15
    @7
    cL
    wcel
    @3
    @12
    @15
    @0
    @1
    @12
    @2
    @13
    3adant3
    #
    adantr
    @16
    @1
    @2
    @15
    @18
    @0
    @1
    @2
    @15
    simpl2
    @0
    @1
    @2
    @15
    simpl3
    @3
    @15
    simpr
    #
    cA
    cB
    cC
    @17
    cP
    cR
    @4
    cM
    cN
    crg
    pm2mpval.p
    pm2mpval.c
    pm2mpval.b
    pm2mpval.a
    @17
    eqid
    #
    decpmatcl
    syl3anc
    #
    @20
    cL
    @5
    @4
    cQ
    cA
    c.as
    c.ex
    @17
    cQ
    cmgp
    cfv
    #
    cX
    @21
    pm2mpval.q
    pm2mpval.x
    pm2mpval.m
    @23
    eqid
    #
    pm2mpval.e
    pm2mpcl.l
    ply1tmcl
    syl3anc
    @8
    eqid
    fmptd
    @3
    @17
    cn0
    cQ
    cQ
    csca
    cfv
    #
    @5
    vk
    c.as
    cL
    cvv
    @6
    @9
    @25
    c0g
    cfv
    #
    @14
    @3
    @12
    cQ
    clmod
    wcel
    @19
    cQ
    cA
    pm2mpval.q
    ply1lmod
    syl
    @3
    @25
    eqidd
    pm2mpcl.l
    @22
    @3
    @12
    @15
    @6
    cL
    wcel
    @19
    cL
    @4
    cQ
    cA
    c.ex
    @23
    cX
    pm2mpval.q
    pm2mpval.x
    @24
    pm2mpval.e
    pm2mpcl.l
    ply1moncl
    sylan
    @10
    @26
    eqid
    pm2mpval.m
    @3
    vk
    cn0
    @5
    cmpt
    #
    cA
    c0g
    cfv
    #
    @26
    cfsupp
    @1
    @2
    @27
    @28
    cfsupp
    wbr
    @0
    cA
    cB
    cC
    cP
    cR
    vk
    cM
    cN
    @28
    pm2mpval.p
    pm2mpval.c
    pm2mpval.b
    pm2mpval.a
    @28
    eqid
    decpmatfsupp
    3adant1
    @3
    @25
    cA
    c0g
    @3
    @12
    @25
    cA
    wceq
    @19
    @12
    cA
    @25
    cQ
    cA
    crg
    pm2mpval.q
    ply1sca
    eqcomd
    syl
    fveq2d
    breqtrrd
    mptscmfsupp0
    gsumcl
    eqeltrd
end
