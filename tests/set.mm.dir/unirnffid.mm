include "crn.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "cuni.mm"
include "wfn.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "fnfi.mm"
include "syl2anc.mm"
include "rnfi.mm"
include "frn.mm"
include "unifi.mm"

theorem unirnffid
  let wph: wff ph
  let cT: class T
  let cF: class F
  assume unirnffid.1: |- ( ph -> F : T --> Fin )
  assume unirnffid.2: |- ( ph -> T e. Fin )


  assert |- ( ph -> U. ran F e. Fin )

  proof
    wph
    cF
    crn
    #
    cfn
    wcel
    #
    @0
    cfn
    wss
    #
    @0
    cuni
    cfn
    wcel
    wph
    cF
    cfn
    wcel
    #
    @1
    wph
    cF
    cT
    wfn
    #
    cT
    cfn
    wcel
    @3
    wph
    cT
    cfn
    cF
    wf
    #
    @4
    unirnffid.1
    cT
    cfn
    cF
    ffn
    syl
    unirnffid.2
    cT
    cF
    fnfi
    syl2anc
    cF
    rnfi
    syl
    wph
    @5
    @2
    unirnffid.1
    cT
    cfn
    cF
    frn
    syl
    @0
    unifi
    syl2anc
end
