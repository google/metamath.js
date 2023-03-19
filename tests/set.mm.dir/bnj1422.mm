include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wfn.mm"
include "df-fn.mm"
include "sylanbrc.mm"

theorem bnj1422
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume bnj1422.1: |- ( ph -> Fun A )
  assume bnj1422.2: |- ( ph -> dom A = B )


  assert |- ( ph -> A Fn B )

  proof
    wph
    cA
    wfun
    cA
    cdm
    cB
    wceq
    cA
    cB
    wfn
    bnj1422.1
    bnj1422.2
    cA
    cB
    df-fn
    sylanbrc
end
