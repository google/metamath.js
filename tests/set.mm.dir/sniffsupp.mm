include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "snfi.mm"
include "cdif.mm"
include "wa.mm"
include "wne.mm"
include "eldifsni.mm"
include "adantl.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "suppss2.mm"
include "ssfi.mm"
include "sylancr.mm"
include "wfun.mm"
include "cvv.mm"
include "wb.mm"
include "funmpt.mm"
include "a1i.mm"
include "mptexg.mm"
include "syl.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "syl5eqbr.mm"

theorem sniffsupp
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume sniffsupp.i: |- ( ph -> I e. V )
  assume sniffsupp.0: |- ( ph -> .0. e. W )
  assume sniffsupp.f: |- F = ( x e. I |-> if ( x = X , A , .0. ) )

  disjoint I x
  disjoint X x
  disjoint .0. x
  disjoint ph x
  assert |- ( ph -> F finSupp .0. )

  proof
    wph
    cF
    vx
    cI
    vx
    cv
    #
    cX
    wceq
    #
    cA
    c.0
    cif
    #
    cmpt
    #
    c.0
    cfsupp
    sniffsupp.f
    wph
    @3
    c.0
    cfsupp
    wbr
    #
    @3
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    cX
    csn
    #
    cfn
    wcel
    @5
    @7
    wss
    @6
    cX
    snfi
    wph
    cI
    @2
    vx
    cV
    @7
    c.0
    wph
    @0
    cI
    @7
    cdif
    wcel
    #
    wa
    #
    @1
    cA
    c.0
    @9
    @0
    cX
    @8
    @0
    cX
    wne
    wph
    @0
    cI
    cX
    eldifsni
    adantl
    neneqd
    iffalsed
    sniffsupp.i
    suppss2
    @7
    @5
    ssfi
    sylancr
    wph
    @3
    wfun
    #
    @3
    cvv
    wcel
    #
    c.0
    cW
    wcel
    @4
    @6
    wb
    @10
    wph
    vx
    cI
    @2
    funmpt
    a1i
    wph
    cI
    cV
    wcel
    @11
    sniffsupp.i
    vx
    cI
    @2
    cV
    mptexg
    syl
    sniffsupp.0
    @3
    cvv
    cW
    c.0
    funisfsupp
    syl3anc
    mpbird
    syl5eqbr
end
