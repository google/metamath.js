include "com.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "ccnv.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "a1i.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "infpssrlem1.mm"
include "eldifad.mm"
include "eqeltrd.mm"
include "wa.mm"
include "wss.mm"
include "adantr.mm"
include "wf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "ffvelrnda.mm"
include "sseldd.mm"
include "infpssrlem2.mm"
include "syl5ibr.mm"
include "expd.mm"
include "finds2.mm"
include "com12.mm"
include "ralrimiv.mm"
include "ffnfv.mm"
include "sylanbrc.mm"

theorem infpssrlem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cM: class M
  let cN: class N
  assume infpssrlem.a: |- ( ph -> B C_ A )
  assume infpssrlem.c: |- ( ph -> F : B -1-1-onto-> A )
  assume infpssrlem.d: |- ( ph -> C e. ( A \ B ) )
  assume infpssrlem.e: |- G = ( rec ( `' F , C ) |` _om )


  assert |- ( ph -> G : _om --> A )

  proof
    wph
    cG
    com
    wfn
    #
    vc
    cv
    #
    cG
    cfv
    #
    cA
    wcel
    #
    vc
    com
    wral
    com
    cA
    cG
    wf
    @0
    wph
    @0
    cF
    ccnv
    #
    cC
    crdg
    com
    cres
    #
    com
    wfn
    cC
    @4
    frfnom
    com
    cG
    @5
    infpssrlem.e
    fneq1i
    mpbir
    a1i
    wph
    @3
    vc
    com
    @1
    com
    wcel
    wph
    @3
    @3
    c0
    cG
    cfv
    #
    cA
    wcel
    vb
    cv
    #
    cG
    cfv
    #
    cA
    wcel
    #
    @7
    csuc
    #
    cG
    cfv
    #
    cA
    wcel
    #
    wph
    vc
    vb
    @1
    c0
    wceq
    @2
    @6
    cA
    @1
    c0
    cG
    fveq2
    eleq1d
    @1
    @7
    wceq
    @2
    @8
    cA
    @1
    @7
    cG
    fveq2
    eleq1d
    @1
    @10
    wceq
    @2
    @11
    cA
    @1
    @10
    cG
    fveq2
    eleq1d
    wph
    @6
    cC
    cA
    wph
    cA
    cB
    cC
    cF
    cG
    infpssrlem.a
    infpssrlem.c
    infpssrlem.d
    infpssrlem.e
    infpssrlem1
    wph
    cC
    cA
    cB
    infpssrlem.d
    eldifad
    eqeltrd
    @7
    com
    wcel
    #
    wph
    @9
    @12
    wph
    @9
    wa
    #
    @12
    @13
    @8
    @4
    cfv
    #
    cA
    wcel
    @14
    cB
    cA
    @15
    wph
    cB
    cA
    wss
    @9
    infpssrlem.a
    adantr
    wph
    cA
    cB
    @8
    @4
    wph
    cB
    cA
    cF
    wf1o
    cA
    cB
    @4
    wf1o
    cA
    cB
    @4
    wf
    infpssrlem.c
    cB
    cA
    cF
    f1ocnv
    cA
    cB
    @4
    f1of
    3syl
    ffvelrnda
    sseldd
    @13
    @11
    @15
    cA
    wph
    cA
    cB
    cC
    cF
    cG
    @7
    infpssrlem.a
    infpssrlem.c
    infpssrlem.d
    infpssrlem.e
    infpssrlem2
    eleq1d
    syl5ibr
    expd
    finds2
    com12
    ralrimiv
    vc
    com
    cA
    cG
    ffnfv
    sylanbrc
end
