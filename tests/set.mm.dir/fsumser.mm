include "cfz.mm"
include "co.mm"
include "csu.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq1d.mm"
include "eqid.mm"
include "fvex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "ifeq1da.mm"
include "sylan9eqr.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "fsumsers.mm"
include "elfzuz.mm"
include "syl.mm"
include "iftrue.mm"
include "eqtrd.mm"
include "adantl.mm"
include "seqfveq.mm"

theorem fsumser
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vm: setvar m
  assume fsumser.1: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) = A )
  assume fsumser.2: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fsumser.3: |- ( ( ph /\ k e. ( M ... N ) ) -> A e. CC )

  disjoint F k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint k m
  disjoint F m
  disjoint M m
  disjoint N m
  assert |- ( ph -> sum_ k e. ( M ... N ) A = ( seq M ( + , F ) ` N ) )

  proof
    wph
    cM
    cN
    cfz
    co
    #
    cA
    vk
    csu
    cN
    caddc
    vm
    cM
    cuz
    cfv
    #
    vm
    cv
    #
    @0
    wcel
    #
    @2
    cF
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    cM
    cseq
    cfv
    cN
    caddc
    cF
    cM
    cseq
    cfv
    wph
    @0
    cA
    vk
    @6
    cM
    cN
    vk
    cv
    #
    @1
    wcel
    #
    wph
    @7
    @6
    cfv
    #
    @7
    @0
    wcel
    #
    @7
    cF
    cfv
    #
    cc0
    cif
    #
    @10
    cA
    cc0
    cif
    vm
    @7
    @5
    @12
    @1
    @6
    @2
    @7
    wceq
    @3
    @10
    @4
    @11
    cc0
    @2
    @7
    @0
    eleq1
    @2
    @7
    cF
    fveq2
    ifbieq1d
    @6
    eqid
    @10
    @11
    cc0
    @7
    cF
    fvex
    c0ex
    ifex
    fvmpt
    #
    wph
    @10
    @11
    cA
    cc0
    fsumser.1
    ifeq1da
    sylan9eqr
    fsumser.2
    fsumser.3
    @0
    @0
    wss
    wph
    @0
    ssid
    a1i
    fsumsers
    wph
    caddc
    vk
    @6
    cF
    cM
    cN
    fsumser.2
    @10
    @9
    @11
    wceq
    wph
    @10
    @9
    @12
    @11
    @10
    @8
    @9
    @12
    wceq
    @7
    cM
    cN
    elfzuz
    @13
    syl
    @10
    @11
    cc0
    iftrue
    eqtrd
    adantl
    seqfveq
    eqtrd
end
