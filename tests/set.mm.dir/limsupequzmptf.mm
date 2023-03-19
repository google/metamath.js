include "cv.mm"
include "csb.mm"
include "cmpt.mm"
include "clsp.mm"
include "cfv.mm"
include "nfv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfel.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "limsupequzmpt.mm"
include "cbvmptf.mm"
include "fveq2i.mm"
include "a1i.mm"
include "3eqtr4d.mm"

theorem limsupequzmptf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let vk: setvar k
  assume limsupequzmptf.j: |- F/ j ph
  assume limsupequzmptf.o: |- F/_ j A
  assume limsupequzmptf.p: |- F/_ j B
  assume limsupequzmptf.m: |- ( ph -> M e. ZZ )
  assume limsupequzmptf.n: |- ( ph -> N e. ZZ )
  assume limsupequzmptf.a: |- A = ( ZZ>= ` M )
  assume limsupequzmptf.b: |- B = ( ZZ>= ` N )
  assume limsupequzmptf.c: |- ( ( ph /\ j e. A ) -> C e. V )
  assume limsupequzmptf.d: |- ( ( ph /\ j e. B ) -> C e. W )

  disjoint V j
  disjoint W j
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint M k
  disjoint N k
  disjoint j k
  disjoint k ph
  assert |- ( ph -> ( limsup ` ( j e. A |-> C ) ) = ( limsup ` ( j e. B |-> C ) ) )

  proof
    wph
    vk
    cA
    vj
    vk
    cv
    #
    cC
    csb
    #
    cmpt
    #
    clsp
    cfv
    #
    vk
    cB
    @1
    cmpt
    #
    clsp
    cfv
    #
    vj
    cA
    cC
    cmpt
    #
    clsp
    cfv
    #
    vj
    cB
    cC
    cmpt
    #
    clsp
    cfv
    #
    wph
    cA
    cB
    @1
    vk
    cM
    cN
    cV
    cW
    wph
    vk
    nfv
    limsupequzmptf.m
    limsupequzmptf.n
    limsupequzmptf.a
    limsupequzmptf.b
    wph
    vj
    cv
    #
    cA
    wcel
    #
    wa
    #
    cC
    cV
    wcel
    #
    wi
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @1
    cV
    wcel
    #
    wi
    vj
    vk
    @15
    @16
    vj
    wph
    @14
    vj
    limsupequzmptf.j
    vj
    vk
    cA
    limsupequzmptf.o
    nfcri
    nfan
    vj
    @1
    cV
    vj
    @0
    cC
    nfcsb1v
    #
    vj
    cV
    nfcv
    nfel
    nfim
    @10
    @0
    wceq
    #
    @12
    @15
    @13
    @16
    @18
    @11
    @14
    wph
    @10
    @0
    cA
    eleq1
    anbi2d
    @18
    cC
    @1
    cV
    vj
    @0
    cC
    csbeq1a
    #
    eleq1d
    imbi12d
    limsupequzmptf.c
    chvar
    wph
    @10
    cB
    wcel
    #
    wa
    #
    cC
    cW
    wcel
    #
    wi
    wph
    @0
    cB
    wcel
    #
    wa
    #
    @1
    cW
    wcel
    #
    wi
    vj
    vk
    @24
    @25
    vj
    wph
    @23
    vj
    limsupequzmptf.j
    vj
    vk
    cB
    limsupequzmptf.p
    nfcri
    nfan
    vj
    @1
    cW
    @17
    vj
    cW
    nfcv
    nfel
    nfim
    @18
    @21
    @24
    @22
    @25
    @18
    @20
    @23
    wph
    @10
    @0
    cB
    eleq1
    anbi2d
    @18
    cC
    @1
    cW
    @19
    eleq1d
    imbi12d
    limsupequzmptf.d
    chvar
    limsupequzmpt
    @7
    @3
    wceq
    wph
    @6
    @2
    clsp
    vj
    vk
    cA
    cC
    @1
    limsupequzmptf.o
    vk
    cA
    nfcv
    vk
    cC
    nfcv
    #
    @17
    @19
    cbvmptf
    fveq2i
    a1i
    @9
    @5
    wceq
    wph
    @8
    @4
    clsp
    vj
    vk
    cB
    cC
    @1
    limsupequzmptf.p
    vk
    cB
    nfcv
    @26
    @17
    @19
    cbvmptf
    fveq2i
    a1i
    3eqtr4d
end
