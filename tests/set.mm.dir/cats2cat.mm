include "cconcat.mm"
include "co.mm"
include "cs1.mm"
include "cs2.mm"
include "oveq12i.mm"
include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "wceq.mm"
include "s1cli.mm"
include "ccatcl.mm"
include "mp2an.mm"
include "ccatass.mm"
include "mp3an.mm"
include "df-s2.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "3eqtr2i.mm"

theorem cats2cat
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let cY: class Y
  assume cats2cat.b: |- B e. Word _V
  assume cats2cat.d: |- D e. Word _V
  assume cats2cat.a: |- A = ( B ++ <" X "> )
  assume cats2cat.c: |- C = ( <" Y "> ++ D )


  assert |- ( A ++ C ) = ( ( B ++ <" X Y "> ) ++ D )

  proof
    cA
    cC
    cconcat
    co
    cB
    cX
    cs1
    #
    cconcat
    co
    #
    cY
    cs1
    #
    cD
    cconcat
    co
    #
    cconcat
    co
    #
    @1
    @2
    cconcat
    co
    #
    cD
    cconcat
    co
    #
    cB
    cX
    cY
    cs2
    #
    cconcat
    co
    #
    cD
    cconcat
    co
    cA
    @1
    cC
    @3
    cconcat
    cats2cat.a
    cats2cat.c
    oveq12i
    @1
    cvv
    cword
    #
    wcel
    #
    @2
    @9
    wcel
    #
    cD
    @9
    wcel
    @6
    @4
    wceq
    cB
    @9
    wcel
    #
    @0
    @9
    wcel
    #
    @10
    cats2cat.b
    cX
    s1cli
    #
    cvv
    cB
    @0
    ccatcl
    mp2an
    cY
    s1cli
    #
    cats2cat.d
    cvv
    @1
    @2
    cD
    ccatass
    mp3an
    @5
    @8
    cD
    cconcat
    @5
    cB
    @0
    @2
    cconcat
    co
    #
    cconcat
    co
    #
    @8
    @12
    @13
    @11
    @5
    @17
    wceq
    cats2cat.b
    @14
    @15
    cvv
    cB
    @0
    @2
    ccatass
    mp3an
    @16
    @7
    cB
    cconcat
    @7
    @16
    cX
    cY
    df-s2
    eqcomi
    oveq2i
    eqtri
    oveq1i
    3eqtr2i
end
