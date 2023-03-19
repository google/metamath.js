include "wfn.mm"
include "wfun.mm"
include "wcel.mm"
include "cdm.mm"
include "fnfun.mm"
include "fndm.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "syl2an2r.mm"

theorem funfni
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  assume funfni.1: |- ( ( Fun F /\ B e. dom F ) -> ph )


  assert |- ( ( F Fn A /\ B e. A ) -> ph )

  proof
    cF
    cA
    wfn
    #
    cF
    wfun
    cB
    cA
    wcel
    #
    cB
    cF
    cdm
    #
    wcel
    #
    wph
    cA
    cF
    fnfun
    @0
    @3
    @1
    @0
    @2
    cA
    cB
    cA
    cF
    fndm
    eleq2d
    biimpar
    funfni.1
    syl2an2r
end
