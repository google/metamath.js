include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "cfsupp.mm"
include "wrel.mm"
include "wceq.mm"
include "wfun.mm"
include "funrel.mm"
include "syl.mm"
include "resindm.mm"
include "wfn.mm"
include "funfn.mm"
include "sylib.mm"
include "fnresin2.mm"
include "cfn.mm"
include "wcel.mm"
include "infi.mm"
include "fndmfifsupp.mm"
include "eqbrtrrd.mm"

theorem resfifsupp
  let wph: wff ph
  let cF: class F
  let cV: class V
  let cX: class X
  let cZ: class Z
  assume resfifsupp.f: |- ( ph -> Fun F )
  assume resfifsupp.x: |- ( ph -> X e. Fin )
  assume resfifsupp.z: |- ( ph -> Z e. V )


  assert |- ( ph -> ( F |` X ) finSupp Z )

  proof
    wph
    cF
    cX
    cF
    cdm
    #
    cin
    #
    cres
    #
    cF
    cX
    cres
    #
    cZ
    cfsupp
    wph
    cF
    wrel
    #
    @2
    @3
    wceq
    wph
    cF
    wfun
    #
    @4
    resfifsupp.f
    cF
    funrel
    syl
    cF
    cX
    resindm
    syl
    wph
    @1
    @2
    cV
    cZ
    wph
    cF
    @0
    wfn
    #
    @2
    @1
    wfn
    wph
    @5
    @6
    resfifsupp.f
    cF
    funfn
    sylib
    @0
    cX
    cF
    fnresin2
    syl
    wph
    cX
    cfn
    wcel
    @1
    cfn
    wcel
    resfifsupp.x
    cX
    @0
    infi
    syl
    resfifsupp.z
    fndmfifsupp
    eqbrtrrd
end
