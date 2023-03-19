include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "chst.mm"
include "chil.mm"
include "eldifi.mm"
include "cheli.mm"
include "syl.mm"
include "hstrlem3a.mm"
include "sylan.mm"
include "sylbi.mm"

theorem hstrlem3
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
  assert |- ( ph -> S e. CHStates )

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
    c1
    wceq
    #
    wa
    cS
    chst
    wcel
    #
    hstrlem3.2
    @1
    @0
    chil
    wcel
    #
    @2
    @3
    @1
    @0
    cA
    wcel
    @4
    @0
    cA
    cB
    eldifi
    @0
    cA
    hstrlem3.3
    cheli
    syl
    vx
    vu
    cS
    hstrlem3.1
    hstrlem3a
    sylan
    sylbi
end
