include "cxp.mm"
include "cvv.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "csb.mm"
include "wcel.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "wa.mm"
include "wceq.mm"
include "wrex.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "nfcv.mm"
include "nfcsb.mm"
include "nfv.mm"
include "cop.mm"
include "csbopeq1a.mm"
include "eqeq2d.mm"
include "rexxpf.mm"
include "sylibr.mm"
include "wdom2d.mm"

theorem wdom2d2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  let vw: setvar w
  assume wdom2d2.a: |- ( ph -> A e. V )
  assume wdom2d2.b: |- ( ph -> B e. W )
  assume wdom2d2.c: |- ( ph -> C e. X )
  assume wdom2d2.o: |- ( ( ph /\ x e. A ) -> E. y e. B E. z e. C x = X )

  disjoint X x
  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint w x
  disjoint X w
  disjoint A w
  disjoint w y
  disjoint B w
  disjoint w z
  disjoint C w
  disjoint ph w
  assert |- ( ph -> A ~<_* ( B X. C ) )

  proof
    wph
    vx
    vw
    cA
    cB
    cC
    cxp
    #
    cV
    cvv
    vy
    vw
    cv
    #
    c1st
    cfv
    #
    vz
    @1
    c2nd
    cfv
    #
    cX
    csb
    #
    csb
    #
    wdom2d2.a
    wph
    cB
    cW
    wcel
    cC
    cX
    wcel
    @0
    cvv
    wcel
    wdom2d2.b
    wdom2d2.c
    cB
    cC
    cW
    cX
    xpexg
    syl2anc
    wph
    vx
    cv
    #
    cA
    wcel
    wa
    @6
    cX
    wceq
    #
    vz
    cC
    wrex
    vy
    cB
    wrex
    @6
    @5
    wceq
    #
    vw
    @0
    wrex
    wdom2d2.o
    @8
    @7
    vw
    vy
    vz
    cB
    cC
    vy
    @6
    @5
    vy
    @2
    @4
    nfcsb1v
    nfeq2
    vz
    @6
    @5
    vz
    vy
    @2
    @4
    vz
    @2
    nfcv
    vz
    @3
    cX
    nfcsb1v
    nfcsb
    nfeq2
    @7
    vw
    nfv
    @1
    vy
    cv
    vz
    cv
    cop
    wceq
    @5
    cX
    @6
    vy
    vz
    @1
    cX
    csbopeq1a
    eqeq2d
    rexxpf
    sylibr
    wdom2d
end
