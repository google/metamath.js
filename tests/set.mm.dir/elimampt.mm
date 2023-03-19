include "cima.mm"
include "wcel.mm"
include "cres.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "df-ima.mm"
include "eleq2i.mm"
include "cmpt.mm"
include "wss.mm"
include "wb.mm"
include "reseq1i.mm"
include "resmpt.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "eleq2d.mm"
include "syl.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "bitrd.mm"
include "syl5bb.mm"

theorem elimampt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cW: class W
  assume elimampt.f: |- F = ( x e. A |-> B )
  assume elimampt.c: |- ( ph -> C e. W )
  assume elimampt.d: |- ( ph -> D C_ A )

  disjoint A x
  disjoint C x
  disjoint D x
  assert |- ( ph -> ( C e. ( F " D ) <-> E. x e. D C = B ) )

  proof
    cC
    cF
    cD
    cima
    #
    wcel
    cC
    cF
    cD
    cres
    #
    crn
    #
    wcel
    #
    wph
    cC
    cB
    wceq
    vx
    cD
    wrex
    #
    @0
    @2
    cC
    cF
    cD
    df-ima
    eleq2i
    wph
    @3
    cC
    vx
    cD
    cB
    cmpt
    #
    crn
    #
    wcel
    #
    @4
    wph
    cD
    cA
    wss
    #
    @3
    @7
    wb
    elimampt.d
    @8
    @2
    @6
    cC
    @8
    @1
    @5
    @8
    @1
    vx
    cA
    cB
    cmpt
    #
    cD
    cres
    @5
    cF
    @9
    cD
    elimampt.f
    reseq1i
    vx
    cA
    cD
    cB
    resmpt
    syl5eq
    rneqd
    eleq2d
    syl
    wph
    cC
    cW
    wcel
    @7
    @4
    wb
    elimampt.c
    vx
    cD
    cB
    cC
    @5
    cW
    @5
    eqid
    elrnmpt
    syl
    bitrd
    syl5bb
end
