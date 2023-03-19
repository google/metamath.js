include "wne.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "3ancoma.mm"
include "wb.mm"
include "orcom.mm"
include "a1i.mm"
include "3anbi3d.mm"
include "syl5bb.mm"
include "ishlg.mm"
include "3bitr4d.mm"

theorem hlcomb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vg: setvar g
  assume ishlg.p: |- P = ( Base ` G )
  assume ishlg.i: |- I = ( Itv ` G )
  assume ishlg.k: |- K = ( hlG ` G )
  assume ishlg.a: |- ( ph -> A e. P )
  assume ishlg.b: |- ( ph -> B e. P )
  assume ishlg.c: |- ( ph -> C e. P )
  assume ishlg.g: |- ( ph -> G e. V )


  assert |- ( ph -> ( A ( K ` C ) B <-> B ( K ` C ) A ) )

  proof
    wph
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    cA
    cC
    cB
    cI
    co
    wcel
    #
    cB
    cC
    cA
    cI
    co
    wcel
    #
    wo
    #
    w3a
    #
    @1
    @0
    @3
    @2
    wo
    #
    w3a
    #
    cA
    cB
    cC
    cK
    cfv
    #
    wbr
    cB
    cA
    @8
    wbr
    @5
    @1
    @0
    @4
    w3a
    wph
    @7
    @0
    @1
    @4
    3ancoma
    wph
    @4
    @6
    @1
    @0
    @4
    @6
    wb
    wph
    @2
    @3
    orcom
    a1i
    3anbi3d
    syl5bb
    wph
    cA
    cB
    cC
    cP
    cG
    cI
    cK
    cV
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.a
    ishlg.b
    ishlg.c
    ishlg.g
    ishlg
    wph
    cB
    cA
    cC
    cP
    cG
    cI
    cK
    cV
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.b
    ishlg.a
    ishlg.c
    ishlg.g
    ishlg
    3bitr4d
end
