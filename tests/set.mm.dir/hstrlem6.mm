include "cfv.mm"
include "cno.mm"
include "c1.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "hstrlem4.mm"
include "chil.mm"
include "wcel.mm"
include "cr.mm"
include "chst.mm"
include "cch.mm"
include "hstrlem3.mm"
include "hstcl.mm"
include "sylancl.mm"
include "normcl.mm"
include "syl.mm"
include "hstrlem5.mm"
include "ltned.mm"
include "neneqd.mm"
include "jca.mm"
include "annim.mm"
include "sylib.mm"

theorem hstrlem6
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
  assert |- ( ph -> -. ( ( normh ` ( S ` A ) ) = 1 -> ( normh ` ( S ` B ) ) = 1 ) )

  proof
    wph
    cA
    cS
    cfv
    cno
    cfv
    c1
    wceq
    #
    cB
    cS
    cfv
    #
    cno
    cfv
    #
    c1
    wceq
    #
    wn
    #
    wa
    @0
    @3
    wi
    wn
    wph
    @0
    @4
    wph
    vx
    vu
    cA
    cB
    cS
    hstrlem3.1
    hstrlem3.2
    hstrlem3.3
    hstrlem3.4
    hstrlem4
    wph
    @2
    c1
    wph
    @2
    c1
    wph
    @1
    chil
    wcel
    #
    @2
    cr
    wcel
    wph
    cS
    chst
    wcel
    cB
    cch
    wcel
    @5
    wph
    vx
    vu
    cA
    cB
    cS
    hstrlem3.1
    hstrlem3.2
    hstrlem3.3
    hstrlem3.4
    hstrlem3
    hstrlem3.4
    cB
    cS
    hstcl
    sylancl
    @1
    normcl
    syl
    wph
    vx
    vu
    cA
    cB
    cS
    hstrlem3.1
    hstrlem3.2
    hstrlem3.3
    hstrlem3.4
    hstrlem5
    ltned
    neneqd
    jca
    @0
    @3
    annim
    sylib
end
