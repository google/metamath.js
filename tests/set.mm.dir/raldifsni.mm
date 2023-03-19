include "wn.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "imbi1i.mm"
include "impexp.mm"
include "df-ne.mm"
include "con34b.mm"
include "bitr4i.mm"
include "imbi2i.mm"
include "3bitri.mm"
include "ralbii2.mm"

theorem raldifsni
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( A. x e. ( A \ { B } ) -. ph <-> A. x e. A ( ph -> x = B ) )

  proof
    wph
    wn
    #
    wph
    vx
    cv
    #
    cB
    wceq
    #
    wi
    #
    vx
    cA
    cB
    csn
    cdif
    #
    cA
    @1
    @4
    wcel
    #
    @0
    wi
    @1
    cA
    wcel
    #
    @1
    cB
    wne
    #
    wa
    #
    @0
    wi
    @6
    @7
    @0
    wi
    #
    wi
    @6
    @3
    wi
    @5
    @8
    @0
    @1
    cA
    cB
    eldifsn
    imbi1i
    @6
    @7
    @0
    impexp
    @9
    @3
    @6
    @9
    @2
    wn
    #
    @0
    wi
    @3
    @7
    @10
    @0
    @1
    cB
    df-ne
    imbi1i
    wph
    @2
    con34b
    bitr4i
    imbi2i
    3bitri
    ralbii2
end
