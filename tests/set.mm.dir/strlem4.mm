include "cfv.mm"
include "cv.mm"
include "cpjh.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cch.mm"
include "wcel.mm"
include "wceq.mm"
include "strlem2.mm"
include "ax-mp.mm"
include "cdif.mm"
include "wa.mm"
include "eldifi.mm"
include "pjid.mm"
include "mpan.mm"
include "fveq2d.mm"
include "eqeq2.mm"
include "syl5ib.mm"
include "mpan9.mm"
include "sylbi.mm"
include "oveq1d.mm"
include "sq1.mm"
include "syl6eq.mm"
include "syl5eq.mm"

theorem strlem4
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
  assert |- ( ph -> ( S ` A ) = 1 )

  proof
    wph
    cA
    cS
    cfv
    #
    vu
    cv
    #
    cA
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    c1
    cA
    cch
    wcel
    #
    @0
    @4
    wceq
    strlem3.3
    vx
    vu
    cA
    cS
    strlem3.1
    strlem2
    ax-mp
    wph
    @4
    c1
    c2
    cexp
    co
    c1
    wph
    @3
    c1
    c2
    cexp
    wph
    @1
    cA
    cB
    cdif
    wcel
    #
    @1
    cno
    cfv
    #
    c1
    wceq
    #
    wa
    @3
    c1
    wceq
    #
    strlem3.2
    @6
    @1
    cA
    wcel
    #
    @8
    @9
    @1
    cA
    cB
    eldifi
    @10
    @3
    @7
    wceq
    @8
    @9
    @10
    @2
    @1
    cno
    @5
    @10
    @2
    @1
    wceq
    strlem3.3
    @1
    cA
    pjid
    mpan
    fveq2d
    @7
    c1
    @3
    eqeq2
    syl5ib
    mpan9
    sylbi
    oveq1d
    sq1
    syl6eq
    syl5eq
end
