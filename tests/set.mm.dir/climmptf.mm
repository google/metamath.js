include "cz.mm"
include "wcel.mm"
include "cli.mm"
include "wbr.mm"
include "wb.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nffv.mm"
include "fveq2.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "climmpt.mm"
include "syl2anc.mm"

theorem climmptf
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vj: setvar j
  assume climmptf.k: |- F/_ k F
  assume climmptf.m: |- ( ph -> M e. ZZ )
  assume climmptf.f: |- ( ph -> F e. V )
  assume climmptf.z: |- Z = ( ZZ>= ` M )
  assume climmptf.g: |- G = ( k e. Z |-> ( F ` k ) )

  disjoint Z k
  disjoint A j
  disjoint F j
  disjoint Z j
  disjoint j k
  assert |- ( ph -> ( F ~~> A <-> G ~~> A ) )

  proof
    wph
    cM
    cz
    wcel
    cF
    cV
    wcel
    cF
    cA
    cli
    wbr
    cG
    cA
    cli
    wbr
    wb
    climmptf.m
    climmptf.f
    cA
    vj
    cF
    cG
    cM
    cV
    cZ
    climmptf.z
    cG
    vk
    cZ
    vk
    cv
    #
    cF
    cfv
    #
    cmpt
    vj
    cZ
    vj
    cv
    #
    cF
    cfv
    #
    cmpt
    climmptf.g
    vk
    vj
    cZ
    @1
    @3
    vj
    @1
    nfcv
    vk
    @2
    cF
    climmptf.k
    vk
    @2
    nfcv
    nffv
    @0
    @2
    cF
    fveq2
    cbvmpt
    eqtri
    climmpt
    syl2anc
end
