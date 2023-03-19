include "cmpt2.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "wral.mm"
include "cv.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylib.mm"
include "cmap.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cfn.mm"
include "wceq.mm"
include "matbas2.mm"
include "syl2anc.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpexg.mm"
include "elmapg.mm"
include "sylancr.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem matbas2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cK: class K
  let cN: class N
  let cV: class V
  assume matbas2.a: |- A = ( N Mat R )
  assume matbas2.k: |- K = ( Base ` R )
  assume matbas2i.b: |- B = ( Base ` A )
  assume matbas2d.n: |- ( ph -> N e. Fin )
  assume matbas2d.r: |- ( ph -> R e. V )
  assume matbas2d.c: |- ( ( ph /\ x e. N /\ y e. N ) -> C e. K )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint K x
  disjoint K y
  assert |- ( ph -> ( x e. N , y e. N |-> C ) e. B )

  proof
    wph
    vx
    vy
    cN
    cN
    cC
    cmpt2
    #
    cB
    wcel
    #
    cN
    cN
    cxp
    #
    cK
    @0
    wf
    #
    wph
    cC
    cK
    wcel
    #
    vy
    cN
    wral
    vx
    cN
    wral
    @3
    wph
    @4
    vx
    vy
    cN
    cN
    wph
    vx
    cv
    cN
    wcel
    vy
    cv
    cN
    wcel
    @4
    matbas2d.c
    3expb
    ralrimivva
    vx
    vy
    cN
    cN
    cC
    cK
    @0
    @0
    eqid
    fmpt2
    sylib
    wph
    @1
    @0
    cK
    @2
    cmap
    co
    #
    wcel
    #
    @3
    wph
    cB
    @5
    @0
    wph
    @5
    cA
    cbs
    cfv
    #
    cB
    wph
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    @5
    @7
    wceq
    matbas2d.n
    matbas2d.r
    cA
    cR
    cK
    cN
    cV
    matbas2.a
    matbas2.k
    matbas2
    syl2anc
    matbas2i.b
    syl6reqr
    eleq2d
    wph
    cK
    cvv
    wcel
    @2
    cvv
    wcel
    #
    @6
    @3
    wb
    cK
    cR
    cbs
    cfv
    cvv
    matbas2.k
    cR
    cbs
    fvex
    eqeltri
    wph
    @8
    @8
    @9
    matbas2d.n
    matbas2d.n
    cN
    cN
    cfn
    cfn
    xpexg
    syl2anc
    cK
    @2
    @0
    cvv
    cvv
    elmapg
    sylancr
    bitrd
    mpbird
end
