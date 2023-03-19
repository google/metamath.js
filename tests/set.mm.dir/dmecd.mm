include "cdm.mm"
include "wcel.mm"
include "cec.mm"
include "c0.mm"
include "wne.mm"
include "neeq1d.mm"
include "ecdmn0.mm"
include "3bitr4g.mm"
include "eleq2d.mm"
include "3bitr3d.mm"

theorem dmecd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume dmecd.1: |- ( ph -> dom R = A )
  assume dmecd.2: |- ( ph -> [ B ] R = [ C ] R )


  assert |- ( ph -> ( B e. A <-> C e. A ) )

  proof
    wph
    cB
    cR
    cdm
    #
    wcel
    #
    cC
    @0
    wcel
    #
    cB
    cA
    wcel
    cC
    cA
    wcel
    wph
    cB
    cR
    cec
    #
    c0
    wne
    cC
    cR
    cec
    #
    c0
    wne
    @1
    @2
    wph
    @3
    @4
    c0
    dmecd.2
    neeq1d
    cB
    cR
    ecdmn0
    cC
    cR
    ecdmn0
    3bitr4g
    wph
    @0
    cA
    cB
    dmecd.1
    eleq2d
    wph
    @0
    cA
    cC
    dmecd.1
    eleq2d
    3bitr3d
end
