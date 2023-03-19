include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cfv.mm"
include "cmat2pmat.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "c0g.mm"
include "cmat.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "0mat2pmat.mm"
include "ancoms.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "cbs.mm"
include "matring.mm"
include "ring0cl.mm"
include "syl.mm"
include "m2cpminvid.mm"
include "mpd3an3.mm"
include "eqtrd.mm"

theorem m2cpminv0
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let cI: class I
  let cN: class N
  let c.0: class .0.
  let cZ: class Z
  assume m2cpminv0.a: |- A = ( N Mat R )
  assume m2cpminv0.i: |- I = ( N cPolyMatToMat R )
  assume m2cpminv0.p: |- P = ( Poly1 ` R )
  assume m2cpminv0.c: |- C = ( N Mat P )
  assume m2cpminv0.0: |- .0. = ( 0g ` A )
  assume m2cpminv0.z: |- Z = ( 0g ` C )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( I ` Z ) = .0. )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cZ
    cI
    cfv
    c.0
    cN
    cR
    cmat2pmat
    co
    #
    cfv
    #
    cI
    cfv
    #
    c.0
    @2
    cZ
    @4
    cI
    @2
    @4
    cZ
    @1
    @0
    @4
    cZ
    wceq
    cP
    cR
    @3
    cN
    c.0
    cZ
    @3
    eqid
    #
    m2cpminv0.p
    c.0
    cA
    c0g
    cfv
    cN
    cR
    cmat
    co
    #
    c0g
    cfv
    m2cpminv0.0
    cA
    @7
    c0g
    m2cpminv0.a
    fveq2i
    eqtri
    cZ
    cC
    c0g
    cfv
    cN
    cP
    cmat
    co
    #
    c0g
    cfv
    m2cpminv0.z
    cC
    @8
    c0g
    m2cpminv0.c
    fveq2i
    eqtri
    0mat2pmat
    ancoms
    eqcomd
    fveq2d
    @0
    @1
    c.0
    cA
    cbs
    cfv
    #
    wcel
    #
    @5
    c.0
    wceq
    @2
    cA
    crg
    wcel
    @10
    cA
    cR
    cN
    m2cpminv0.a
    matring
    @9
    cA
    c.0
    @9
    eqid
    #
    m2cpminv0.0
    ring0cl
    syl
    cA
    cR
    @3
    cI
    @9
    c.0
    cN
    m2cpminv0.i
    m2cpminv0.a
    @11
    @6
    m2cpminvid
    mpd3an3
    eqtrd
end
