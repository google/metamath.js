include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cdecpmat.mm"
include "co.mm"
include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "decpmatval.mm"
include "3adant1.mm"
include "cbs.mm"
include "eqid.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "3ad2ant1.mm"
include "matecld.mm"
include "coe1fvalcl.mm"
include "syl2anc.mm"
include "matbas2d.mm"
include "eqeltrd.mm"

theorem decpmatcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vj: setvar j
  assume decpmate.p: |- P = ( Poly1 ` R )
  assume decpmate.c: |- C = ( N Mat P )
  assume decpmate.b: |- B = ( Base ` C )
  assume decpmatcl.a: |- A = ( N Mat R )
  assume decpmatcl.d: |- D = ( Base ` A )


  assert |- ( ( R e. V /\ M e. B /\ K e. NN0 ) -> ( M decompPMat K ) e. D )

  proof
    cR
    cV
    wcel
    #
    cM
    cB
    wcel
    #
    cK
    cn0
    wcel
    #
    w3a
    #
    cM
    cK
    cdecpmat
    co
    #
    vi
    vj
    cN
    cN
    cK
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    cD
    @1
    @2
    @4
    @10
    wceq
    @0
    cC
    cB
    cP
    vi
    vj
    cK
    cM
    cN
    decpmate.c
    decpmate.b
    decpmatval
    3adant1
    @3
    vi
    vj
    cA
    cD
    @9
    cR
    cR
    cbs
    cfv
    #
    cN
    cV
    decpmatcl.a
    @11
    eqid
    #
    decpmatcl.d
    @1
    @0
    cN
    cfn
    wcel
    #
    @2
    @1
    @13
    cP
    cvv
    wcel
    cC
    cB
    cP
    cN
    cM
    decpmate.c
    decpmate.b
    matrcl
    simpld
    3ad2ant2
    @0
    @1
    @2
    simp1
    @3
    @5
    cN
    wcel
    #
    @6
    cN
    wcel
    #
    w3a
    #
    @7
    cP
    cbs
    cfv
    #
    wcel
    @2
    @9
    @11
    wcel
    @16
    cC
    cB
    cP
    @5
    @6
    @17
    cM
    cN
    decpmate.c
    @17
    eqid
    #
    decpmate.b
    @3
    @14
    @15
    simp2
    @3
    @14
    @15
    simp3
    @3
    @14
    @1
    @15
    @0
    @1
    @2
    simp2
    3ad2ant1
    matecld
    @3
    @14
    @2
    @15
    @0
    @1
    @2
    simp3
    3ad2ant1
    @8
    @17
    cP
    cR
    @7
    @11
    cK
    @8
    eqid
    @18
    decpmate.p
    @12
    coe1fvalcl
    syl2anc
    matbas2d
    eqeltrd
end
