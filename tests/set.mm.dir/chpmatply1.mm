include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cfv.mm"
include "cv1.mm"
include "cmat.mm"
include "co.mm"
include "cur.mm"
include "cvsca.mm"
include "cmat2pmat.mm"
include "csg.mm"
include "cmdat.mm"
include "eqid.mm"
include "chpmatval.mm"
include "cbs.mm"
include "ply1crng.mm"
include "3ad2ant2.mm"
include "crg.mm"
include "crngring.mm"
include "chmatcl.mm"
include "syl3an2.mm"
include "mdetcl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem chpmatply1
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cE: class E
  let cM: class M
  let cN: class N
  let vp: setvar p
  let vx: setvar x
  assume chpmatply1.c: |- C = ( N CharPlyMat R )
  assume chpmatply1.a: |- A = ( N Mat R )
  assume chpmatply1.b: |- B = ( Base ` A )
  assume chpmatply1.p: |- P = ( Poly1 ` R )
  assume chpmatply1.e: |- E = ( Base ` P )


  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> ( C ` M ) e. E )

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
    cM
    cC
    cfv
    cR
    cv1
    cfv
    #
    cN
    cP
    cmat
    co
    #
    cur
    cfv
    #
    @5
    cvsca
    cfv
    #
    co
    cM
    cN
    cR
    cmat2pmat
    co
    #
    cfv
    @5
    csg
    cfv
    #
    co
    #
    cN
    cP
    cmdat
    co
    #
    cfv
    #
    cE
    cA
    cB
    cC
    @11
    cP
    cR
    @8
    @7
    @6
    cM
    @9
    cN
    ccrg
    @4
    @5
    chpmatply1.c
    chpmatply1.a
    chpmatply1.b
    chpmatply1.p
    @5
    eqid
    #
    @11
    eqid
    #
    @9
    eqid
    #
    @4
    eqid
    #
    @7
    eqid
    #
    @8
    eqid
    #
    @6
    eqid
    #
    chpmatval
    @3
    cP
    ccrg
    wcel
    #
    @10
    @5
    cbs
    cfv
    #
    wcel
    #
    @12
    cE
    wcel
    @1
    @0
    @20
    @2
    cP
    cR
    chpmatply1.p
    ply1crng
    3ad2ant2
    @1
    @0
    cR
    crg
    wcel
    @2
    @22
    cR
    crngring
    cA
    cB
    cP
    cR
    @8
    @7
    @6
    @10
    cM
    @9
    cN
    @4
    @5
    chpmatply1.a
    chpmatply1.b
    chpmatply1.p
    @13
    @16
    @18
    @15
    @17
    @19
    @10
    eqid
    chmatcl
    syl3an2
    @5
    @21
    @11
    cP
    cE
    @10
    cN
    @14
    @13
    @21
    eqid
    chpmatply1.e
    mdetcl
    syl2anc
    eqeltrd
end
