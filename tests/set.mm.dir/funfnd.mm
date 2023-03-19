include "wfun.mm"
include "cdm.mm"
include "wfn.mm"
include "funfn.mm"
include "sylib.mm"

theorem funfnd
  let wph: wff ph
  let cA: class A
  assume funfnd.1: |- ( ph -> Fun A )


  assert |- ( ph -> A Fn dom A )

  proof
    wph
    cA
    wfun
    cA
    cA
    cdm
    wfn
    funfnd.1
    cA
    funfn
    sylib
end
