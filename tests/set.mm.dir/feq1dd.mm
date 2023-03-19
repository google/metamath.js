include "wf.mm"
include "feq1d.mm"
include "mpbid.mm"

theorem feq1dd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume feq1dd.eq: |- ( ph -> F = G )
  assume feq1dd.f: |- ( ph -> F : A --> B )


  assert |- ( ph -> G : A --> B )

  proof
    wph
    cA
    cB
    cF
    wf
    cA
    cB
    cG
    wf
    feq1dd.f
    wph
    cA
    cB
    cF
    cG
    feq1dd.eq
    feq1d
    mpbid
end
