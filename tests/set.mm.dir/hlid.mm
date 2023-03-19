include "cfv.mm"
include "wbr.mm"
include "wne.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "w3a.mm"
include "cds.mm"
include "eqid.mm"
include "tgbtwntriv2.mm"
include "olcd.mm"
include "3jca.mm"
include "cstrkg.mm"
include "ishlg.mm"
include "mpbird.mm"

theorem hlid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
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
  assume hlid.1: |- ( ph -> A =/= C )


  assert |- ( ph -> A ( K ` C ) A )

  proof
    wph
    cA
    cA
    cC
    cK
    cfv
    wbr
    cA
    cC
    wne
    #
    @0
    cA
    cC
    cA
    cI
    co
    wcel
    #
    @1
    wo
    #
    w3a
    wph
    @0
    @0
    @2
    hlid.1
    hlid.1
    wph
    @1
    @1
    wph
    cC
    cA
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    ishlg.p
    @3
    eqid
    ishlg.i
    hlln.1
    ishlg.c
    ishlg.a
    tgbtwntriv2
    olcd
    3jca
    wph
    cA
    cA
    cC
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.a
    ishlg.a
    ishlg.c
    hlln.1
    ishlg
    mpbird
end
