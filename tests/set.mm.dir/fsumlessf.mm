include "cv.mm"
include "csb.mm"
include "csu.mm"
include "cle.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "cc0.mm"
include "nfcv.mm"
include "nfbr.mm"
include "breq2d.mm"
include "fsumless.mm"
include "cbvsum.mm"
include "breq12i.mm"
include "sylibr.mm"

theorem fsumlessf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vj: setvar j
  assume fsumlessf.k: |- F/ k ph
  assume fsumge0.a: |- ( ph -> A e. Fin )
  assume fsumge0.b: |- ( ( ph /\ k e. A ) -> B e. RR )
  assume fsumge0.l: |- ( ( ph /\ k e. A ) -> 0 <_ B )
  assume fsumless.c: |- ( ph -> C C_ A )

  disjoint A k
  disjoint C k
  disjoint A j
  disjoint j k
  disjoint B j
  disjoint C j
  disjoint j ph
  assert |- ( ph -> sum_ k e. C B <_ sum_ k e. A B )

  proof
    wph
    cC
    vk
    vj
    cv
    #
    cB
    csb
    #
    vj
    csu
    #
    cA
    @1
    vj
    csu
    #
    cle
    wbr
    cC
    cB
    vk
    csu
    #
    cA
    cB
    vk
    csu
    #
    cle
    wbr
    wph
    cA
    @1
    cC
    vj
    fsumge0.a
    wph
    vk
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    cr
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
    cr
    wcel
    #
    wi
    vk
    vj
    @11
    @12
    vk
    wph
    @10
    vk
    fsumlessf.k
    @10
    vk
    nfv
    nfan
    #
    vk
    @1
    cr
    vk
    @0
    cB
    nfcsb1v
    #
    nfel1
    nfim
    @6
    @0
    wceq
    #
    @8
    @11
    @9
    @12
    @15
    @7
    @10
    wph
    @6
    @0
    cA
    eleq1
    anbi2d
    #
    @15
    cB
    @1
    cr
    vk
    @0
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    fsumge0.b
    chvar
    @8
    cc0
    cB
    cle
    wbr
    #
    wi
    @11
    cc0
    @1
    cle
    wbr
    #
    wi
    vk
    vj
    @11
    @19
    vk
    @13
    vk
    cc0
    @1
    cle
    vk
    cc0
    nfcv
    vk
    cle
    nfcv
    @14
    nfbr
    nfim
    @15
    @8
    @11
    @18
    @19
    @16
    @15
    cB
    @1
    cc0
    cle
    @17
    breq2d
    imbi12d
    fsumge0.l
    chvar
    fsumless.c
    fsumless
    @4
    @2
    @5
    @3
    cle
    cC
    cB
    @1
    vk
    vj
    @17
    vj
    cC
    nfcv
    vk
    cC
    nfcv
    vj
    cB
    nfcv
    #
    @14
    cbvsum
    cA
    cB
    @1
    vk
    vj
    @17
    vj
    cA
    nfcv
    vk
    cA
    nfcv
    @20
    @14
    cbvsum
    breq12i
    sylibr
end
