include "cprod.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cmul.mm"
include "co.mm"
include "nfcvd.mm"
include "fprodsplit1f.mm"
include "cfn.mm"
include "wcel.mm"
include "diffi.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "cc.mm"
include "simpl.mm"
include "eldifi.mm"
include "adantl.mm"
include "syl2anc.mm"
include "fprodclf.mm"
include "mul02d.mm"
include "eqtrd.mm"

theorem fprodeq0g
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume fprodeq0g.kph: |- F/ k ph
  assume fprodeq0g.a: |- ( ph -> A e. Fin )
  assume fprodeq0g.b: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fprodeq0g.c: |- ( ph -> C e. A )
  assume fprodeq0g.b0: |- ( ( ph /\ k = C ) -> B = 0 )

  disjoint A k
  disjoint C k
  assert |- ( ph -> prod_ k e. A B = 0 )

  proof
    wph
    cA
    cB
    vk
    cprod
    cc0
    cA
    cC
    csn
    #
    cdif
    #
    cB
    vk
    cprod
    #
    cmul
    co
    cc0
    wph
    cA
    cB
    cC
    cc0
    vk
    fprodeq0g.kph
    wph
    vk
    cc0
    nfcvd
    fprodeq0g.a
    fprodeq0g.b
    fprodeq0g.c
    fprodeq0g.b0
    fprodsplit1f
    wph
    @2
    wph
    @1
    cB
    vk
    fprodeq0g.kph
    wph
    cA
    cfn
    wcel
    @1
    cfn
    wcel
    fprodeq0g.a
    cA
    @0
    diffi
    syl
    wph
    vk
    cv
    #
    @1
    wcel
    #
    wa
    wph
    @3
    cA
    wcel
    #
    cB
    cc
    wcel
    wph
    @4
    simpl
    @4
    @5
    wph
    @3
    cA
    @0
    eldifi
    adantl
    fprodeq0g.b
    syl2anc
    fprodclf
    mul02d
    eqtrd
end
