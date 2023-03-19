include "cprod.mm"
include "csn.mm"
include "cdif.mm"
include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjdif.mm"
include "a1i.mm"
include "cun.mm"
include "wss.mm"
include "snssd.mm"
include "undif.mm"
include "sylib.mm"
include "eqcomd.mm"
include "fprodsplit.mm"
include "wcel.mm"
include "cc.mm"
include "0cnd.mm"
include "eqeltrd.mm"
include "prodsn.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "cfn.mm"
include "diffi.mm"
include "syl.mm"
include "cv.mm"
include "difssd.mm"
include "sselda.mm"
include "syldan.mm"
include "fprodcl.mm"
include "mul02d.mm"
include "3eqtrd.mm"

theorem fprodeq02
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cK: class K
  assume fprodeq02.1: |- ( k = K -> B = C )
  assume fprodeq02.a: |- ( ph -> A e. Fin )
  assume fprodeq02.b: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fprodeq02.k: |- ( ph -> K e. A )
  assume fprodeq02.c: |- ( ph -> C = 0 )

  disjoint A k
  disjoint C k
  disjoint K k
  disjoint k ph
  assert |- ( ph -> prod_ k e. A B = 0 )

  proof
    wph
    cA
    cB
    vk
    cprod
    cK
    csn
    #
    cB
    vk
    cprod
    #
    cA
    @0
    cdif
    #
    cB
    vk
    cprod
    #
    cmul
    co
    cc0
    @3
    cmul
    co
    cc0
    wph
    @0
    @2
    cB
    cA
    vk
    @0
    @2
    cin
    c0
    wceq
    wph
    @0
    cA
    disjdif
    a1i
    wph
    @0
    @2
    cun
    #
    cA
    wph
    @0
    cA
    wss
    @4
    cA
    wceq
    wph
    cK
    cA
    fprodeq02.k
    snssd
    @0
    cA
    undif
    sylib
    eqcomd
    fprodeq02.a
    fprodeq02.b
    fprodsplit
    wph
    @1
    cc0
    @3
    cmul
    wph
    @1
    cC
    cc0
    wph
    cK
    cA
    wcel
    cC
    cc
    wcel
    @1
    cC
    wceq
    fprodeq02.k
    wph
    cC
    cc0
    cc
    fprodeq02.c
    wph
    0cnd
    eqeltrd
    cB
    cC
    vk
    cK
    cA
    fprodeq02.1
    prodsn
    syl2anc
    fprodeq02.c
    eqtrd
    oveq1d
    wph
    @3
    wph
    @2
    cB
    vk
    wph
    cA
    cfn
    wcel
    @2
    cfn
    wcel
    fprodeq02.a
    cA
    @0
    diffi
    syl
    wph
    vk
    cv
    #
    @2
    wcel
    @5
    cA
    wcel
    cB
    cc
    wcel
    wph
    @2
    cA
    @5
    wph
    cA
    @0
    difssd
    sselda
    fprodeq02.b
    syldan
    fprodcl
    mul02d
    3eqtrd
end
