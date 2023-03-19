include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "wdfat.mm"
include "dmeqd.mm"
include "eleq12d.mm"
include "sneqd.mm"
include "reseq12d.mm"
include "funeqd.mm"
include "anbi12d.mm"
include "df-dfat.mm"
include "3bitr4g.mm"

theorem dfateq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x
  assume dfateq12d.1: |- ( ph -> F = G )
  assume dfateq12d.2: |- ( ph -> A = B )


  assert |- ( ph -> ( F defAt A <-> G defAt B ) )

  proof
    wph
    cA
    cF
    cdm
    #
    wcel
    #
    cF
    cA
    csn
    #
    cres
    #
    wfun
    #
    wa
    cB
    cG
    cdm
    #
    wcel
    #
    cG
    cB
    csn
    #
    cres
    #
    wfun
    #
    wa
    cA
    cF
    wdfat
    cB
    cG
    wdfat
    wph
    @1
    @6
    @4
    @9
    wph
    cA
    cB
    @0
    @5
    dfateq12d.2
    wph
    cF
    cG
    dfateq12d.1
    dmeqd
    eleq12d
    wph
    @3
    @8
    wph
    cF
    cG
    @2
    @7
    dfateq12d.1
    wph
    cA
    cB
    dfateq12d.2
    sneqd
    reseq12d
    funeqd
    anbi12d
    cA
    cF
    df-dfat
    cB
    cG
    df-dfat
    3bitr4g
end
