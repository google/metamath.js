include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cn0.mm"
include "wral.mm"
include "wa.mm"
include "cco1.mm"
include "cv1.mm"
include "cmgp.mm"
include "cmg.mm"
include "co.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wi.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspccv.mm"
include "adantl.mm"
include "imp.mm"
include "fveq1i.mm"
include "3eqtr3g.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "wb.mm"
include "eqid.mm"
include "ply1coe.mm"
include "3adant3.mm"
include "3adant2.mm"
include "adantr.mm"
include "mpbird.mm"
include "ex.mm"

theorem eqcoe1ply1eq
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let vk: setvar k
  let cK: class K
  let cL: class L
  let vn: setvar n
  assume eqcoe1ply1eq.p: |- P = ( Poly1 ` R )
  assume eqcoe1ply1eq.b: |- B = ( Base ` P )
  assume eqcoe1ply1eq.a: |- A = ( coe1 ` K )
  assume eqcoe1ply1eq.c: |- C = ( coe1 ` L )

  disjoint A k
  disjoint C k
  disjoint A n
  disjoint k n
  disjoint B n
  disjoint C n
  disjoint K n
  disjoint L n
  disjoint P n
  disjoint R n
  assert |- ( ( R e. Ring /\ K e. B /\ L e. B ) -> ( A. k e. NN0 ( A ` k ) = ( C ` k ) -> K = L ) )

  proof
    cR
    crg
    wcel
    #
    cK
    cB
    wcel
    #
    cL
    cB
    wcel
    #
    w3a
    #
    vk
    cv
    #
    cA
    cfv
    #
    @4
    cC
    cfv
    #
    wceq
    #
    vk
    cn0
    wral
    #
    cK
    cL
    wceq
    #
    @3
    @8
    wa
    #
    @9
    cP
    vn
    cn0
    vn
    cv
    #
    cK
    cco1
    cfv
    #
    cfv
    #
    @11
    cR
    cv1
    cfv
    #
    cP
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    cP
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
    cP
    vn
    cn0
    @11
    cL
    cco1
    cfv
    #
    cfv
    #
    @17
    @18
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    @10
    @20
    @25
    cP
    cgsu
    @10
    vn
    cn0
    @19
    @24
    @10
    @11
    cn0
    wcel
    #
    wa
    #
    @13
    @23
    @17
    @18
    @29
    @11
    cA
    cfv
    #
    @11
    cC
    cfv
    #
    @13
    @23
    @10
    @28
    @30
    @31
    wceq
    #
    @8
    @28
    @32
    wi
    @3
    @7
    @32
    vk
    @11
    cn0
    @4
    @11
    wceq
    @5
    @30
    @6
    @31
    @4
    @11
    cA
    fveq2
    @4
    @11
    cC
    fveq2
    eqeq12d
    rspccv
    adantl
    imp
    @11
    cA
    @12
    eqcoe1ply1eq.a
    fveq1i
    @11
    cC
    @22
    eqcoe1ply1eq.c
    fveq1i
    3eqtr3g
    oveq1d
    mpteq2dva
    oveq2d
    @3
    @9
    @27
    wb
    @8
    @3
    cK
    @21
    cL
    @26
    @0
    @1
    cK
    @21
    wceq
    @2
    @12
    cB
    cP
    cR
    @18
    vn
    @16
    cK
    @15
    @14
    eqcoe1ply1eq.p
    @14
    eqid
    #
    eqcoe1ply1eq.b
    @18
    eqid
    #
    @15
    eqid
    #
    @16
    eqid
    #
    @12
    eqid
    ply1coe
    3adant3
    @0
    @2
    cL
    @26
    wceq
    @1
    @22
    cB
    cP
    cR
    @18
    vn
    @16
    cL
    @15
    @14
    eqcoe1ply1eq.p
    @33
    eqcoe1ply1eq.b
    @34
    @35
    @36
    @22
    eqid
    ply1coe
    3adant2
    eqeq12d
    adantr
    mpbird
    ex
end
