include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cpw.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "wal.mm"
include "vex.mm"
include "inex2.mm"
include "inss1.mm"
include "elmapintrab.mm"
include "elin.mm"
include "imbi2i.mm"
include "jcab.mm"
include "bitri.mm"
include "albii.mm"
include "19.26.mm"
include "19.23v.mm"
include "anbi1i.mm"
include "anbi2i.mm"
include "anabs5.mm"
include "syl6bb.mm"

theorem elinintrab
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint ph w
  disjoint w x
  disjoint A w
  disjoint A x
  disjoint B w
  disjoint B x
  assert |- ( A e. V -> ( A e. |^| { w e. ~P B | E. x ( w = ( B i^i x ) /\ ph ) } <-> ( ( E. x ph -> A e. B ) /\ A. x ( ph -> A e. x ) ) ) )

  proof
    cA
    cV
    wcel
    cA
    vw
    cv
    cB
    vx
    cv
    #
    cin
    #
    wceq
    wph
    wa
    vx
    wex
    vw
    cB
    cpw
    crab
    cint
    wcel
    wph
    vx
    wex
    cA
    cB
    wcel
    #
    wi
    #
    wph
    cA
    @1
    wcel
    #
    wi
    #
    vx
    wal
    #
    wa
    #
    @3
    wph
    cA
    @0
    wcel
    #
    wi
    #
    vx
    wal
    #
    wa
    #
    wph
    vx
    vw
    cA
    cB
    @1
    cV
    @0
    cB
    vx
    vex
    inex2
    cB
    @0
    inss1
    elmapintrab
    @7
    @3
    @11
    wa
    @11
    @6
    @11
    @3
    @6
    wph
    @2
    wi
    #
    @9
    wa
    #
    vx
    wal
    #
    @11
    @5
    @13
    vx
    @5
    wph
    @2
    @8
    wa
    #
    wi
    @13
    @4
    @15
    wph
    cA
    cB
    @0
    elin
    imbi2i
    wph
    @2
    @8
    jcab
    bitri
    albii
    @14
    @12
    vx
    wal
    #
    @10
    wa
    @11
    @12
    @9
    vx
    19.26
    @16
    @3
    @10
    wph
    @2
    vx
    19.23v
    anbi1i
    bitri
    bitri
    anbi2i
    @3
    @10
    anabs5
    bitri
    syl6bb
end
