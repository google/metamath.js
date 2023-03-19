include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "wa.mm"
include "crg.mm"
include "cbs.mm"
include "simpl1.mm"
include "crngring.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "eqid.mm"
include "chpmatply1.mm"
include "syl5eqel.mm"
include "coe1fvalcl.mm"
include "sylan.mm"
include "anim2i.mm"
include "matring.mm"
include "ringidcl.mm"
include "3syl.mm"
include "3adant3.mm"
include "matvscl.mm"
include "syl22anc.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "nn0ex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "mpbird.mm"

theorem cpmidpmatlem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vk: setvar k
  let c.ex: class .^
  let cG: class G
  let cH: class H
  let c.as: class .*
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let cL: class L
  let vn: setvar n
  let vl: setvar l
  let vx: setvar x
  assume cpmidgsum.a: |- A = ( N Mat R )
  assume cpmidgsum.b: |- B = ( Base ` A )
  assume cpmidgsum.p: |- P = ( Poly1 ` R )
  assume cpmidgsum.y: |- Y = ( N Mat P )
  assume cpmidgsum.x: |- X = ( var1 ` R )
  assume cpmidgsum.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume cpmidgsum.m: |- .x. = ( .s ` Y )
  assume cpmidgsum.1: |- .1. = ( 1r ` Y )
  assume cpmidgsum.u: |- U = ( algSc ` P )
  assume cpmidgsum.c: |- C = ( N CharPlyMat R )
  assume cpmidgsum.k: |- K = ( C ` M )
  assume cpmidgsum.h: |- H = ( K .x. .1. )
  assume cpmidgsumm2pm.o: |- O = ( 1r ` A )
  assume cpmidgsumm2pm.m: |- .* = ( .s ` A )
  assume cpmidgsumm2pm.t: |- T = ( N matToPolyMat R )
  assume cpmidpmat.g: |- G = ( k e. NN0 |-> ( ( ( coe1 ` K ) ` k ) .* O ) )

  disjoint K k
  disjoint O k
  disjoint .* k
  disjoint M k
  disjoint B k
  disjoint H k
  disjoint N k
  disjoint P k
  disjoint R k
  disjoint Y k
  disjoint L k
  disjoint A n
  disjoint B n
  disjoint k n
  disjoint H n
  disjoint K n
  disjoint X n
  disjoint N l
  disjoint N n
  disjoint N x
  disjoint k l
  disjoint k x
  disjoint l n
  disjoint l x
  disjoint n x
  disjoint P n
  disjoint R n
  disjoint Y l
  disjoint Y n
  disjoint .^ n
  disjoint M n
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> G e. ( B ^m NN0 ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cG
    cB
    cn0
    cmap
    co
    wcel
    #
    cn0
    cB
    cG
    wf
    #
    @3
    vk
    cn0
    vk
    cv
    #
    cK
    cco1
    cfv
    #
    cfv
    #
    cO
    c.as
    co
    #
    cB
    cG
    @3
    @6
    cn0
    wcel
    #
    wa
    @0
    cR
    crg
    wcel
    #
    @8
    cR
    cbs
    cfv
    #
    wcel
    #
    cO
    cB
    wcel
    #
    @9
    cB
    wcel
    @0
    @1
    @2
    @10
    simpl1
    @3
    @11
    @10
    @1
    @0
    @11
    @2
    cR
    crngring
    #
    3ad2ant2
    adantr
    @3
    cK
    cP
    cbs
    cfv
    #
    wcel
    @10
    @13
    @3
    cK
    cM
    cC
    cfv
    @16
    cpmidgsum.k
    cA
    cB
    cC
    cP
    cR
    @16
    cM
    cN
    cpmidgsum.c
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsum.p
    @16
    eqid
    #
    chpmatply1
    syl5eqel
    @7
    @16
    cP
    cR
    cK
    @12
    @6
    @7
    eqid
    @17
    cpmidgsum.p
    @12
    eqid
    #
    coe1fvalcl
    sylan
    @3
    @14
    @10
    @0
    @1
    @14
    @2
    @0
    @1
    wa
    @0
    @11
    wa
    cA
    crg
    wcel
    @14
    @1
    @11
    @0
    @15
    anim2i
    cA
    cR
    cN
    cpmidgsum.a
    matring
    cB
    cA
    cO
    cpmidgsum.b
    cpmidgsumm2pm.o
    ringidcl
    3syl
    3adant3
    adantr
    cA
    cB
    @8
    cR
    c.as
    @12
    cN
    cO
    @18
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsumm2pm.m
    matvscl
    syl22anc
    cpmidpmat.g
    fmptd
    cB
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    #
    wa
    @4
    @5
    wb
    @3
    @19
    @20
    cB
    cA
    cbs
    cfv
    cvv
    cpmidgsum.b
    cA
    cbs
    fvex
    eqeltri
    nn0ex
    pm3.2i
    cB
    cn0
    cG
    cvv
    cvv
    elmapg
    mp1i
    mpbird
end
