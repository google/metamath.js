include "cfv.mm"
include "wbr.mm"
include "wne.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "w3a.mm"
include "cds.mm"
include "eqid.mm"
include "tgbtwncom.mm"
include "orcd.mm"
include "3jca.mm"
include "cstrkg.mm"
include "ishlg.mm"
include "mpbird.mm"

theorem btwnhl2
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
  assume btwnhl2.3: |- ( ph -> C =/= B )


  assert |- ( ph -> C ( K ` B ) A )

  proof
    wph
    cC
    cA
    cB
    cK
    cfv
    wbr
    cC
    cB
    wne
    #
    cA
    cB
    wne
    #
    cC
    cB
    cA
    cI
    co
    wcel
    #
    cA
    cB
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
    btwnhl2.3
    btwnhl1.2
    wph
    @2
    @3
    wph
    cA
    cC
    cB
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    ishlg.p
    @5
    eqid
    ishlg.i
    hlln.1
    ishlg.a
    ishlg.c
    ishlg.b
    btwnhl1.1
    tgbtwncom
    orcd
    3jca
    wph
    cC
    cA
    cB
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.c
    ishlg.a
    ishlg.b
    hlln.1
    ishlg
    mpbird
end
