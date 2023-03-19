include "wcel.mm"
include "cvv.mm"
include "wor.mm"
include "wpo.mm"
include "cmap.mm"
include "co.mm"
include "elex.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wn.mm"
include "simpll3.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "poirr.mm"
include "syl2anc.mm"
include "intnanrd.mm"
include "nrexdv.mm"
include "wb.mm"
include "vex.mm"
include "wemaplem1.mm"
include "mp2an.mm"
include "sylnibr.mm"
include "simpll1.mm"
include "simplr1.mm"
include "simplr2.mm"
include "simplr3.mm"
include "simpll2.mm"
include "simprl.mm"
include "simprr.mm"
include "wemaplem3.mm"
include "ex.mm"
include "ispod.mm"
include "syl3an1.mm"

theorem wemappo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cU: class U
  let cX: class X
  let cP: class P
  let cQ: class Q
  let cZ: class Z
  assume wemapso.t: |- T = { <. x , y >. | E. z e. A ( ( x ` z ) S ( y ` z ) /\ A. w e. A ( w R z -> ( x ` w ) = ( y ` w ) ) ) }

  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint B b
  disjoint c d
  disjoint c x
  disjoint B c
  disjoint d x
  disjoint B d
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint X a
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint X b
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint X c
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q d
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint Z c
  disjoint Z d
  disjoint Z x
  assert |- ( ( A e. V /\ R Or A /\ S Po B ) -> T Po ( B ^m A ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    cA
    cR
    wor
    #
    cB
    cS
    wpo
    #
    cB
    cA
    cmap
    co
    #
    cT
    wpo
    cA
    cV
    elex
    @0
    @1
    @2
    w3a
    #
    va
    vb
    vc
    @3
    cT
    @4
    va
    cv
    #
    @3
    wcel
    #
    wa
    #
    vb
    cv
    #
    @5
    cfv
    #
    @9
    cS
    wbr
    #
    vc
    cv
    #
    @8
    cR
    wbr
    @11
    @5
    cfv
    #
    @12
    wceq
    wi
    vc
    cA
    wral
    #
    wa
    #
    vb
    cA
    wrex
    #
    @5
    @5
    cT
    wbr
    #
    @7
    @14
    vb
    cA
    @7
    @8
    cA
    wcel
    #
    wa
    #
    @10
    @13
    @18
    @2
    @9
    cB
    wcel
    @10
    wn
    @0
    @1
    @2
    @6
    @17
    simpll3
    @7
    cA
    cB
    @8
    @5
    @6
    cA
    cB
    @5
    wf
    @4
    @5
    cB
    cA
    elmapi
    adantl
    ffvelrnda
    cB
    @9
    cS
    poirr
    syl2anc
    intnanrd
    nrexdv
    @5
    cvv
    wcel
    #
    @19
    @16
    @15
    wb
    va
    vex
    #
    @20
    vx
    vy
    vz
    vw
    cA
    @5
    @5
    cR
    cS
    cT
    cvv
    cvv
    vb
    vc
    wemapso.t
    wemaplem1
    mp2an
    sylnibr
    @4
    @6
    @8
    @3
    wcel
    #
    @11
    @3
    wcel
    #
    w3a
    #
    wa
    #
    @5
    @8
    cT
    wbr
    #
    @8
    @11
    cT
    wbr
    #
    wa
    #
    @5
    @11
    cT
    wbr
    @24
    @27
    wa
    vx
    vy
    vz
    vw
    cA
    cB
    @5
    @11
    cR
    cS
    cT
    @8
    wemapso.t
    @0
    @1
    @2
    @23
    @27
    simpll1
    @6
    @21
    @22
    @4
    @27
    simplr1
    @6
    @21
    @22
    @4
    @27
    simplr2
    @6
    @21
    @22
    @4
    @27
    simplr3
    @0
    @1
    @2
    @23
    @27
    simpll2
    @0
    @1
    @2
    @23
    @27
    simpll3
    @24
    @25
    @26
    simprl
    @24
    @25
    @26
    simprr
    wemaplem3
    ex
    ispod
    syl3an1
end
