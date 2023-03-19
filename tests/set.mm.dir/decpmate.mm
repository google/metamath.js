include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cdecpmat.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "decpmatval.mm"
include "3adant1.mm"
include "adantr.mm"
include "oveq12.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "fvexd.mm"
include "ovmpt2d.mm"

theorem decpmate
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vj: setvar j
  assume decpmate.p: |- P = ( Poly1 ` R )
  assume decpmate.c: |- C = ( N Mat P )
  assume decpmate.b: |- B = ( Base ` C )


  assert |- ( ( ( R e. V /\ M e. B /\ K e. NN0 ) /\ ( I e. N /\ J e. N ) ) -> ( I ( M decompPMat K ) J ) = ( ( coe1 ` ( I M J ) ) ` K ) )

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
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    wa
    #
    wa
    #
    vi
    vj
    cI
    cJ
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
    cK
    cI
    cJ
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cM
    cK
    cdecpmat
    co
    #
    cvv
    @3
    @16
    vi
    vj
    cN
    cN
    @12
    cmpt2
    wceq
    #
    @6
    @1
    @2
    @17
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
    adantr
    @8
    cI
    wceq
    @9
    cJ
    wceq
    wa
    #
    @12
    @15
    wceq
    @7
    @18
    cK
    @11
    @14
    @18
    @10
    @13
    cco1
    @8
    cI
    @9
    cJ
    cM
    oveq12
    fveq2d
    fveq1d
    adantl
    @3
    @4
    @5
    simprl
    @3
    @4
    @5
    simprr
    @7
    cK
    @14
    fvexd
    ovmpt2d
end
