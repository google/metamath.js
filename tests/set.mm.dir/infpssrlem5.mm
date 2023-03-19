include "com.mm"
include "wf1.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "infpssrlem3.mm"
include "wa.mm"
include "wo.mm"
include "wn.mm"
include "wne.mm"
include "simpll.mm"
include "simplrr.mm"
include "simpr.mm"
include "infpssrlem4.mm"
include "syl3anc.mm"
include "necomd.mm"
include "simplrl.mm"
include "jaodan.mm"
include "ex.mm"
include "necon2bd.mm"
include "wb.mm"
include "word.mm"
include "nnord.mm"
include "ordtri3.mm"
include "syl2an.mm"
include "adantl.mm"
include "sylibrd.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "f1domg.mm"
include "syl5com.mm"

theorem infpssrlem5
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cV: class V
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cM: class M
  let cN: class N
  assume infpssrlem.a: |- ( ph -> B C_ A )
  assume infpssrlem.c: |- ( ph -> F : B -1-1-onto-> A )
  assume infpssrlem.d: |- ( ph -> C e. ( A \ B ) )
  assume infpssrlem.e: |- G = ( rec ( `' F , C ) |` _om )


  assert |- ( ph -> ( A e. V -> _om ~<_ A ) )

  proof
    wph
    com
    cA
    cG
    wf1
    #
    cA
    cV
    wcel
    com
    cA
    cdom
    wbr
    wph
    com
    cA
    cG
    wf
    vb
    cv
    #
    cG
    cfv
    #
    vc
    cv
    #
    cG
    cfv
    #
    wceq
    #
    @1
    @3
    wceq
    #
    wi
    #
    vc
    com
    wral
    vb
    com
    wral
    @0
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
    infpssrlem3
    wph
    @7
    vb
    vc
    com
    com
    wph
    @1
    com
    wcel
    #
    @3
    com
    wcel
    #
    wa
    #
    wa
    #
    @5
    @1
    @3
    wcel
    #
    @3
    @1
    wcel
    #
    wo
    #
    wn
    #
    @6
    @11
    @14
    @2
    @4
    @11
    @14
    @2
    @4
    wne
    #
    @11
    @12
    @16
    @13
    @11
    @12
    wa
    #
    @4
    @2
    @17
    wph
    @9
    @12
    @4
    @2
    wne
    wph
    @10
    @12
    simpll
    wph
    @8
    @9
    @12
    simplrr
    @11
    @12
    simpr
    wph
    cA
    cB
    cC
    cF
    cG
    @3
    @1
    infpssrlem.a
    infpssrlem.c
    infpssrlem.d
    infpssrlem.e
    infpssrlem4
    syl3anc
    necomd
    @11
    @13
    wa
    wph
    @8
    @13
    @16
    wph
    @10
    @13
    simpll
    wph
    @8
    @9
    @13
    simplrl
    @11
    @13
    simpr
    wph
    cA
    cB
    cC
    cF
    cG
    @1
    @3
    infpssrlem.a
    infpssrlem.c
    infpssrlem.d
    infpssrlem.e
    infpssrlem4
    syl3anc
    jaodan
    ex
    necon2bd
    @10
    @6
    @15
    wb
    #
    wph
    @8
    @1
    word
    @3
    word
    @18
    @9
    @1
    nnord
    @3
    nnord
    @1
    @3
    ordtri3
    syl2an
    adantl
    sylibrd
    ralrimivva
    vb
    vc
    com
    cA
    cG
    dff13
    sylanbrc
    com
    cA
    cV
    cG
    f1domg
    syl5com
end
