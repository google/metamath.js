include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "simpl2.mm"
include "breq1.mm"
include "rspcev.mm"
include "3ad2antl3.mm"
include "wb.mm"
include "simpl1.mm"
include "islln.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem llni
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cK: class K
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vp: setvar p
  let vx: setvar x
  assume llnset.b: |- B = ( Base ` K )
  assume llnset.c: |- C = ( <o ` K )
  assume llnset.a: |- A = ( Atoms ` K )
  assume llnset.n: |- N = ( LLines ` K )


  assert |- ( ( ( K e. D /\ X e. B /\ P e. A ) /\ P C X ) -> X e. N )

  proof
    cK
    cD
    wcel
    #
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    cP
    cX
    cC
    wbr
    #
    wa
    #
    cX
    cN
    wcel
    #
    @1
    vp
    cv
    #
    cX
    cC
    wbr
    #
    vp
    cA
    wrex
    #
    @0
    @1
    @2
    @3
    simpl2
    @2
    @0
    @3
    @8
    @1
    @7
    @3
    vp
    cP
    cA
    @6
    cP
    cX
    cC
    breq1
    rspcev
    3ad2antl3
    @4
    @0
    @5
    @1
    @8
    wa
    wb
    @0
    @1
    @2
    @3
    simpl1
    cA
    cB
    cC
    cD
    cK
    cN
    cX
    vp
    llnset.b
    llnset.c
    llnset.a
    llnset.n
    islln
    syl
    mpbir2and
end
