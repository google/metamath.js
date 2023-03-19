include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cpjh.mm"
include "cch.mm"
include "hstrlem2.mm"
include "fveq2d.mm"
include "ax-mp.mm"
include "wn.mm"
include "eldif.mm"
include "chil.mm"
include "cheli.mm"
include "wb.mm"
include "pjnel.mm"
include "mpan.mm"
include "biimpa.mm"
include "sylan.mm"
include "sylbi.mm"
include "breq2.mm"
include "syl5ib.mm"
include "impcom.mm"
include "syl5eqbr.mm"

theorem hstrlem5
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  assume hstrlem3.1: |- S = ( x e. CH |-> ( ( projh ` x ) ` u ) )
  assume hstrlem3.2: |- ( ph <-> ( u e. ( A \ B ) /\ ( normh ` u ) = 1 ) )
  assume hstrlem3.3: |- A e. CH
  assume hstrlem3.4: |- B e. CH

  disjoint ph x
  disjoint u x
  disjoint A x
  disjoint B x
  assert |- ( ph -> ( normh ` ( S ` B ) ) < 1 )

  proof
    wph
    vu
    cv
    #
    cA
    cB
    cdif
    wcel
    #
    @0
    cno
    cfv
    #
    c1
    wceq
    #
    wa
    #
    cB
    cS
    cfv
    #
    cno
    cfv
    #
    c1
    clt
    wbr
    hstrlem3.2
    @4
    @6
    @0
    cB
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    c1
    clt
    cB
    cch
    wcel
    #
    @6
    @8
    wceq
    hstrlem3.4
    @9
    @5
    @7
    cno
    vx
    vu
    cB
    cS
    hstrlem3.1
    hstrlem2
    fveq2d
    ax-mp
    @3
    @1
    @8
    c1
    clt
    wbr
    #
    @1
    @8
    @2
    clt
    wbr
    #
    @3
    @10
    @1
    @0
    cA
    wcel
    #
    @0
    cB
    wcel
    wn
    #
    wa
    @11
    @0
    cA
    cB
    eldif
    @12
    @0
    chil
    wcel
    #
    @13
    @11
    @0
    cA
    hstrlem3.3
    cheli
    @14
    @13
    @11
    @9
    @14
    @13
    @11
    wb
    hstrlem3.4
    @0
    cB
    pjnel
    mpan
    biimpa
    sylan
    sylbi
    @2
    c1
    @8
    clt
    breq2
    syl5ib
    impcom
    syl5eqbr
    sylbi
end
