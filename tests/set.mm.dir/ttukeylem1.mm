include "cvv.mm"
include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wss.mm"
include "wi.mm"
include "elex.mm"
include "a1i.mm"
include "wa.mm"
include "cdom.mm"
include "wbr.mm"
include "id.mm"
include "cuni.mm"
include "cdif.mm"
include "cun.mm"
include "ssun1.mm"
include "undif1.mm"
include "sseqtr4i.mm"
include "ccrd.mm"
include "cfv.mm"
include "wfo.mm"
include "fvex.mm"
include "wf1o.mm"
include "f1ofo.mm"
include "syl.mm"
include "fornex.mm"
include "mpsyl.mm"
include "unexg.mm"
include "syl2anc.mm"
include "ssexg.mm"
include "sylancr.mm"
include "uniexb.mm"
include "sylibr.mm"
include "syl2anr.mm"
include "infpwfidom.mm"
include "reldom.mm"
include "brrelexi.mm"
include "3syl.mm"
include "ex.mm"
include "cv.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "eleq1.mm"
include "pweq.mm"
include "ineq1d.mm"
include "sseq1d.mm"
include "bibi12d.mm"
include "spcgv.mm"
include "syl5com.mm"
include "pm5.21ndd.mm"

theorem ttukeylem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let va: setvar a
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let vf: setvar f
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cG: class G
  assume ttukeylem.1: |- ( ph -> F : ( card ` ( U. A \ B ) ) -1-1-onto-> ( U. A \ B ) )
  assume ttukeylem.2: |- ( ph -> B e. A )
  assume ttukeylem.3: |- ( ph -> A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) )

  disjoint C x
  disjoint A x
  disjoint B x
  disjoint F x
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint a f
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint G a
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint a ph
  disjoint f ph
  disjoint ph u
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint A a
  disjoint A f
  disjoint A u
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint B a
  disjoint B f
  disjoint B u
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint F z
  assert |- ( ph -> ( C e. A <-> ( ~P C i^i Fin ) C_ A ) )

  proof
    wph
    cC
    cvv
    wcel
    #
    cC
    cA
    wcel
    #
    cC
    cpw
    #
    cfn
    cin
    #
    cA
    wss
    #
    @1
    @0
    wi
    wph
    cC
    cA
    elex
    a1i
    wph
    @4
    @0
    wph
    @4
    wa
    @3
    cvv
    wcel
    #
    cC
    @3
    cdom
    wbr
    @0
    @4
    @4
    cA
    cvv
    wcel
    #
    @5
    wph
    @4
    id
    wph
    cA
    cuni
    #
    cvv
    wcel
    #
    @6
    wph
    @7
    @7
    cB
    cdif
    #
    cB
    cun
    #
    wss
    @10
    cvv
    wcel
    #
    @8
    @7
    @7
    cB
    cun
    @10
    @7
    cB
    ssun1
    @7
    cB
    undif1
    sseqtr4i
    wph
    @9
    cvv
    wcel
    #
    cB
    cA
    wcel
    @11
    @9
    ccrd
    cfv
    #
    cvv
    wcel
    wph
    @13
    @9
    cF
    wfo
    #
    @12
    @9
    ccrd
    fvex
    wph
    @13
    @9
    cF
    wf1o
    @14
    ttukeylem.1
    @13
    @9
    cF
    f1ofo
    syl
    @13
    @9
    cvv
    cF
    fornex
    mpsyl
    ttukeylem.2
    @9
    cB
    cvv
    cA
    unexg
    syl2anc
    @7
    @10
    cvv
    ssexg
    sylancr
    cA
    uniexb
    sylibr
    @3
    cA
    cvv
    ssexg
    syl2anr
    cC
    infpwfidom
    cC
    @3
    cdom
    reldom
    brrelexi
    3syl
    ex
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @15
    cpw
    #
    cfn
    cin
    #
    cA
    wss
    #
    wb
    #
    vx
    wal
    @0
    @1
    @4
    wb
    #
    ttukeylem.3
    @20
    @21
    vx
    cC
    cvv
    @15
    cC
    wceq
    #
    @16
    @1
    @19
    @4
    @15
    cC
    cA
    eleq1
    @22
    @18
    @3
    cA
    @22
    @17
    @2
    cfn
    @15
    cC
    pweq
    ineq1d
    sseq1d
    bibi12d
    spcgv
    syl5com
    pm5.21ndd
end
