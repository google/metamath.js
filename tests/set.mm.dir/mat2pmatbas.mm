include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cascl.mm"
include "cmpt2.mm"
include "cbs.mm"
include "eqid.mm"
include "mat2pmatval.mm"
include "cvv.mm"
include "simp1.mm"
include "cpl1.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wf.mm"
include "csca.mm"
include "ply1ring.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "asclf.mm"
include "wceq.mm"
include "ply1sca.mm"
include "fveq2d.mm"
include "feq2d.mm"
include "mpbird.mm"
include "simp2.mm"
include "simp3.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "matecl.mm"
include "syl3anc.mm"
include "ffvelrnd.mm"
include "matbas2d.mm"
include "eqeltrd.mm"

theorem mat2pmatbas
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume mat2pmatbas.t: |- T = ( N matToPolyMat R )
  assume mat2pmatbas.a: |- A = ( N Mat R )
  assume mat2pmatbas.b: |- B = ( Base ` A )
  assume mat2pmatbas.p: |- P = ( Poly1 ` R )
  assume mat2pmatbas.c: |- C = ( N Mat P )


  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> ( T ` M ) e. ( Base ` C ) )

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
    vx
    vy
    cN
    cN
    vx
    cv
    #
    vy
    cv
    #
    cM
    co
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    cmpt2
    cC
    cbs
    cfv
    #
    vx
    vy
    cA
    cB
    cP
    cR
    @7
    cT
    cM
    cN
    crg
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    @7
    eqid
    #
    mat2pmatval
    @3
    vx
    vy
    cC
    @9
    @8
    cP
    cP
    cbs
    cfv
    #
    cN
    cvv
    mat2pmatbas.c
    @11
    eqid
    #
    @9
    eqid
    @0
    @1
    @2
    simp1
    cP
    cvv
    wcel
    @3
    cP
    cR
    cpl1
    cfv
    cvv
    mat2pmatbas.p
    cR
    cpl1
    fvex
    eqeltri
    a1i
    @3
    @4
    cN
    wcel
    #
    @5
    cN
    wcel
    #
    w3a
    #
    cR
    cbs
    cfv
    #
    @11
    @6
    @7
    @15
    @16
    @11
    @7
    wf
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    @11
    @7
    wf
    @15
    @7
    @11
    @17
    @18
    cP
    @10
    @17
    eqid
    @3
    @13
    cP
    crg
    wcel
    #
    @14
    @1
    @0
    @19
    @2
    cP
    cR
    mat2pmatbas.p
    ply1ring
    3ad2ant2
    3ad2ant1
    @3
    @13
    cP
    clmod
    wcel
    #
    @14
    @1
    @0
    @20
    @2
    cP
    cR
    mat2pmatbas.p
    ply1lmod
    3ad2ant2
    3ad2ant1
    @18
    eqid
    @12
    asclf
    @15
    @16
    @18
    @11
    @7
    @3
    @13
    @16
    @18
    wceq
    #
    @14
    @1
    @0
    @21
    @2
    @1
    cR
    @17
    cbs
    cP
    cR
    crg
    mat2pmatbas.p
    ply1sca
    fveq2d
    3ad2ant2
    3ad2ant1
    feq2d
    mpbird
    @15
    @13
    @14
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    @6
    @16
    wcel
    @3
    @13
    @14
    simp2
    @3
    @13
    @14
    simp3
    @3
    @13
    @23
    @14
    @2
    @0
    @23
    @1
    @2
    @23
    cB
    @22
    cM
    mat2pmatbas.b
    eleq2i
    biimpi
    3ad2ant3
    3ad2ant1
    cA
    cR
    @4
    @5
    @16
    cM
    cN
    mat2pmatbas.a
    @16
    eqid
    matecl
    syl3anc
    ffvelrnd
    matbas2d
    eqeltrd
end
