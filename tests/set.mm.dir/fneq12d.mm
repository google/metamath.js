include "wfn.mm"
include "fneq1d.mm"
include "fneq2d.mm"
include "bitrd.mm"

theorem fneq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume fneq12d.1: |- ( ph -> F = G )
  assume fneq12d.2: |- ( ph -> A = B )


  assert |- ( ph -> ( F Fn A <-> G Fn B ) )

  proof
    wph
    cF
    cA
    wfn
    cG
    cA
    wfn
    cG
    cB
    wfn
    wph
    cA
    cF
    cG
    fneq12d.1
    fneq1d
    wph
    cA
    cB
    cG
    fneq12d.2
    fneq2d
    bitrd
end
