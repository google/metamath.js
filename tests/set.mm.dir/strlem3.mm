include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cst.mm"
include "chil.mm"
include "eldifi.mm"
include "cheli.mm"
include "syl.mm"
include "strlem3a.mm"
include "sylan.mm"
include "sylbi.mm"

theorem strlem3
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  assume strlem3.1: |- S = ( x e. CH |-> ( ( normh ` ( ( projh ` x ) ` u ) ) ^ 2 ) )
  assume strlem3.2: |- ( ph <-> ( u e. ( A \ B ) /\ ( normh ` u ) = 1 ) )
  assume strlem3.3: |- A e. CH
  assume strlem3.4: |- B e. CH

  disjoint ph x
  disjoint u x
  disjoint A x
  disjoint B x
  assert |- ( ph -> S e. States )

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
    cst
    wcel
    #
    strlem3.2
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
    strlem3.3
    cheli
    syl
    vx
    vu
    cS
    strlem3.1
    strlem3a
    sylan
    sylbi
end
