include "cfv.mm"
include "cno.mm"
include "cv.mm"
include "cpjh.mm"
include "c1.mm"
include "cch.mm"
include "wcel.mm"
include "wceq.mm"
include "hstrlem2.mm"
include "ax-mp.mm"
include "fveq2i.mm"
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
include "syl5eq.mm"

theorem hstrlem4
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
  assert |- ( ph -> ( normh ` ( S ` A ) ) = 1 )

  proof
    wph
    cA
    cS
    cfv
    #
    cno
    cfv
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
    c1
    @0
    @2
    cno
    cA
    cch
    wcel
    #
    @0
    @2
    wceq
    hstrlem3.3
    vx
    vu
    cA
    cS
    hstrlem3.1
    hstrlem2
    ax-mp
    fveq2i
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
    hstrlem3.2
    @5
    @1
    cA
    wcel
    #
    @7
    @8
    @1
    cA
    cB
    eldifi
    @9
    @3
    @6
    wceq
    @7
    @8
    @9
    @2
    @1
    cno
    @4
    @9
    @2
    @1
    wceq
    hstrlem3.3
    @1
    cA
    pjid
    mpan
    fveq2d
    @6
    c1
    @3
    eqeq2
    syl5ib
    mpan9
    sylbi
    syl5eq
end
