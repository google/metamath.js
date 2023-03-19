include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "ply1ring.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "chpdmatlem0.mm"
include "3adant3.mm"
include "mat2pmatbas.mm"
include "jca.mm"
include "simpr.mm"
include "eqid.mm"
include "matsubgcell.mm"
include "syl112anc.mm"
include "cmulr.mm"
include "cur.mm"
include "vr1cl.mm"
include "adantl.mm"
include "pmatring.mm"
include "ringidcl.mm"
include "syl.mm"
include "matvscacell.mm"
include "c0g.mm"
include "cif.mm"
include "simpl1.mm"
include "mat1ov.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "ringridm.mm"
include "3eqtrd.mm"
include "mat2pmatvalel.mm"
include "anabsan2.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem chpdmatlem3
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.1: class .1.
  let cG: class G
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  assume chpdmat.c: |- C = ( N CharPlyMat R )
  assume chpdmat.p: |- P = ( Poly1 ` R )
  assume chpdmat.a: |- A = ( N Mat R )
  assume chpdmat.s: |- S = ( algSc ` P )
  assume chpdmat.b: |- B = ( Base ` A )
  assume chpdmat.x: |- X = ( var1 ` R )
  assume chpdmat.0: |- .0. = ( 0g ` R )
  assume chpdmat.g: |- G = ( mulGrp ` P )
  assume chpdmat.m: |- .- = ( -g ` P )
  assume chpdmatlem.q: |- Q = ( N Mat P )
  assume chpdmatlem.1: |- .1. = ( 1r ` Q )
  assume chpdmatlem.m: |- .x. = ( .s ` Q )
  assume chpdmatlem.z: |- Z = ( -g ` Q )
  assume chpdmatlem.t: |- T = ( N matToPolyMat R )


  assert |- ( ( ( N e. Fin /\ R e. Ring /\ M e. B ) /\ K e. N ) -> ( K ( ( X .x. .1. ) Z ( T ` M ) ) K ) = ( X .- ( S ` ( K M K ) ) ) )

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
    cK
    cN
    wcel
    #
    wa
    #
    cK
    cK
    cX
    c.1
    c.x
    co
    #
    cM
    cT
    cfv
    #
    cZ
    co
    co
    #
    cK
    cK
    @6
    co
    #
    cK
    cK
    @7
    co
    #
    c.mi
    co
    #
    cX
    cK
    cK
    cM
    co
    cS
    cfv
    #
    c.mi
    co
    @5
    cP
    crg
    wcel
    #
    @6
    cQ
    cbs
    cfv
    #
    wcel
    #
    @7
    @14
    wcel
    #
    wa
    #
    @4
    @4
    @8
    @11
    wceq
    @3
    @13
    @4
    @1
    @0
    @13
    @2
    cP
    cR
    chpdmat.p
    ply1ring
    #
    3ad2ant2
    adantr
    #
    @3
    @17
    @4
    @3
    @15
    @16
    @0
    @1
    @15
    @2
    cA
    cB
    cC
    cP
    cQ
    cR
    cS
    c.x
    c.1
    cG
    c.mi
    cN
    cX
    c.0
    chpdmat.c
    chpdmat.p
    chpdmat.a
    chpdmat.s
    chpdmat.b
    chpdmat.x
    chpdmat.0
    chpdmat.g
    chpdmat.m
    chpdmatlem.q
    chpdmatlem.1
    chpdmatlem.m
    chpdmatlem0
    3adant3
    cA
    cB
    cQ
    cP
    cR
    cT
    cM
    cN
    chpdmatlem.t
    chpdmat.a
    chpdmat.b
    chpdmat.p
    chpdmatlem.q
    mat2pmatbas
    jca
    adantr
    @3
    @4
    simpr
    #
    @20
    cQ
    @14
    cP
    cZ
    cK
    cK
    c.mi
    cN
    @6
    @7
    chpdmatlem.q
    @14
    eqid
    #
    chpdmatlem.z
    chpdmat.m
    matsubgcell
    syl112anc
    @5
    @9
    cX
    @10
    @12
    c.mi
    @5
    @9
    cX
    cK
    cK
    c.1
    co
    #
    cP
    cmulr
    cfv
    #
    co
    #
    cX
    cP
    cur
    cfv
    #
    @23
    co
    #
    cX
    @5
    @13
    cX
    cP
    cbs
    cfv
    #
    wcel
    #
    c.1
    @14
    wcel
    #
    wa
    #
    @4
    @4
    @9
    @24
    wceq
    @19
    @3
    @30
    @4
    @0
    @1
    @30
    @2
    @0
    @1
    wa
    #
    @28
    @29
    @1
    @28
    @0
    @27
    cP
    cR
    cX
    chpdmat.x
    chpdmat.p
    @27
    eqid
    #
    vr1cl
    #
    adantl
    @31
    cQ
    crg
    wcel
    @29
    cQ
    cP
    cR
    cN
    chpdmat.p
    chpdmatlem.q
    pmatring
    @14
    cQ
    c.1
    @21
    chpdmatlem.1
    ringidcl
    syl
    jca
    3adant3
    adantr
    @20
    @20
    cQ
    @14
    cP
    c.x
    @23
    cK
    cK
    @27
    cN
    cX
    c.1
    chpdmatlem.q
    @21
    @32
    chpdmatlem.m
    @23
    eqid
    #
    matvscacell
    syl112anc
    @5
    @22
    @25
    cX
    @23
    @5
    @22
    cK
    cK
    wceq
    #
    @25
    cP
    c0g
    cfv
    #
    cif
    @25
    @5
    cQ
    cP
    c.1
    @25
    cK
    cK
    cN
    @36
    chpdmatlem.q
    @25
    eqid
    #
    @36
    eqid
    @0
    @1
    @2
    @4
    simpl1
    @19
    @20
    @20
    chpdmatlem.1
    mat1ov
    @35
    @25
    @36
    cK
    eqid
    iftruei
    syl6eq
    oveq2d
    @3
    @26
    cX
    wceq
    #
    @4
    @3
    @13
    @28
    wa
    #
    @38
    @1
    @0
    @39
    @2
    @1
    @13
    @28
    @18
    @33
    jca
    3ad2ant2
    @27
    cP
    @23
    @25
    cX
    @32
    @34
    @37
    ringridm
    syl
    adantr
    3eqtrd
    @3
    @4
    @10
    @12
    wceq
    cA
    cB
    cP
    cR
    cS
    cT
    cM
    cN
    crg
    cK
    cK
    chpdmatlem.t
    chpdmat.a
    chpdmat.b
    chpdmat.p
    chpdmat.s
    mat2pmatvalel
    anabsan2
    oveq12d
    eqtrd
end
