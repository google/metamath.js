include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "strlem4.mm"
include "cst.mm"
include "wcel.mm"
include "cch.mm"
include "cr.mm"
include "strlem3.mm"
include "stcl.mm"
include "mpisyl.mm"
include "strlem5.mm"
include "ltned.mm"
include "neneqd.mm"
include "jca.mm"
include "annim.mm"
include "sylib.mm"

theorem strlem6
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
  assert |- ( ph -> -. ( ( S ` A ) = 1 -> ( S ` B ) = 1 ) )

  proof
    wph
    cA
    cS
    cfv
    c1
    wceq
    #
    cB
    cS
    cfv
    #
    c1
    wceq
    #
    wn
    #
    wa
    @0
    @2
    wi
    wn
    wph
    @0
    @3
    wph
    vx
    vu
    cA
    cB
    cS
    strlem3.1
    strlem3.2
    strlem3.3
    strlem3.4
    strlem4
    wph
    @1
    c1
    wph
    @1
    c1
    wph
    cS
    cst
    wcel
    cB
    cch
    wcel
    @1
    cr
    wcel
    wph
    vx
    vu
    cA
    cB
    cS
    strlem3.1
    strlem3.2
    strlem3.3
    strlem3.4
    strlem3
    strlem3.4
    cB
    cS
    stcl
    mpisyl
    wph
    vx
    vu
    cA
    cB
    cS
    strlem3.1
    strlem3.2
    strlem3.3
    strlem3.4
    strlem5
    ltned
    neneqd
    jca
    @0
    @2
    annim
    sylib
end
