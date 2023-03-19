include "cfv.mm"
include "wbr.mm"
include "wne.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "w3a.mm"
include "necomd.mm"
include "orcd.mm"
include "3jca.mm"
include "cstrkg.mm"
include "ishlg.mm"
include "mpbird.mm"

theorem btwnhl1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  assume ishlg.p: |- P = ( Base ` G )
  assume ishlg.i: |- I = ( Itv ` G )
  assume ishlg.k: |- K = ( hlG ` G )
  assume ishlg.a: |- ( ph -> A e. P )
  assume ishlg.b: |- ( ph -> B e. P )
  assume ishlg.c: |- ( ph -> C e. P )
  assume hlln.1: |- ( ph -> G e. TarskiG )
  assume hltr.d: |- ( ph -> D e. P )
  assume btwnhl1.1: |- ( ph -> C e. ( A I B ) )
  assume btwnhl1.2: |- ( ph -> A =/= B )
  assume btwnhl1.3: |- ( ph -> C =/= A )


  assert |- ( ph -> C ( K ` A ) B )

  proof
    wph
    cC
    cB
    cA
    cK
    cfv
    wbr
    cC
    cA
    wne
    #
    cB
    cA
    wne
    #
    cC
    cA
    cB
    cI
    co
    wcel
    #
    cB
    cA
    cC
    cI
    co
    wcel
    #
    wo
    #
    w3a
    wph
    @0
    @1
    @4
    btwnhl1.3
    wph
    cA
    cB
    btwnhl1.2
    necomd
    wph
    @2
    @3
    btwnhl1.1
    orcd
    3jca
    wph
    cC
    cB
    cA
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.c
    ishlg.b
    ishlg.a
    hlln.1
    ishlg
    mpbird
end
