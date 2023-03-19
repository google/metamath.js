include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "citg.mm"
include "cdit.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cif.mm"
include "cicc.mm"
include "cr.mm"
include "ioossicc.mm"
include "sseli.mm"
include "adantl.mm"
include "adantr.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "simpr.mm"
include "cxr.mm"
include "wb.mm"
include "rexrd.mm"
include "elioo2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp2d.mm"
include "gtned.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "simp1d.mm"
include "simp3d.mm"
include "ltned.mm"
include "eqtrd.mm"
include "ffvelrnda.mm"
include "eqeltrd.mm"
include "fvmpt2.mm"
include "3eqtrrd.mm"
include "itgeq2dv.mm"
include "ditgpos.mm"
include "3eqtr4d.mm"

theorem ditgeqiooicc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let cL: class L
  let vk: setvar k
  assume ditgeqiooicc.1: |- G = ( x e. ( A [,] B ) |-> if ( x = A , R , if ( x = B , L , ( F ` x ) ) ) )
  assume ditgeqiooicc.2: |- ( ph -> A e. RR )
  assume ditgeqiooicc.3: |- ( ph -> B e. RR )
  assume ditgeqiooicc.4: |- ( ph -> A <_ B )
  assume ditgeqiooicc.5: |- ( ph -> F : ( A (,) B ) --> RR )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> S_ [ A -> B ] ( F ` x ) _d x = S_ [ A -> B ] ( G ` x ) _d x )

  proof
    wph
    vx
    cA
    cB
    cioo
    co
    #
    vx
    cv
    #
    cF
    cfv
    #
    citg
    vx
    @0
    @1
    cG
    cfv
    #
    citg
    vx
    cA
    cB
    @2
    cdit
    vx
    cA
    cB
    @3
    cdit
    wph
    vx
    @0
    @2
    @3
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @3
    @1
    cA
    wceq
    #
    cR
    @1
    cB
    wceq
    #
    cL
    @2
    cif
    #
    cif
    #
    @8
    @2
    @5
    @1
    cA
    cB
    cicc
    co
    #
    wcel
    #
    @9
    cr
    wcel
    @3
    @9
    wceq
    @4
    @11
    wph
    @0
    @10
    @1
    cA
    cB
    ioossicc
    sseli
    adantl
    @5
    @9
    @2
    cr
    @5
    @9
    @8
    @2
    @5
    @6
    cR
    @8
    @5
    @1
    cA
    @5
    cA
    @1
    wph
    cA
    cr
    wcel
    @4
    ditgeqiooicc.2
    adantr
    #
    @5
    @1
    cr
    wcel
    #
    cA
    @1
    clt
    wbr
    #
    @1
    cB
    clt
    wbr
    #
    @5
    @4
    @13
    @14
    @15
    w3a
    #
    wph
    @4
    simpr
    @5
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @4
    @16
    wb
    @5
    cA
    @12
    rexrd
    @5
    cB
    wph
    cB
    cr
    wcel
    @4
    ditgeqiooicc.3
    adantr
    rexrd
    cA
    cB
    @1
    elioo2
    syl2anc
    mpbid
    #
    simp2d
    gtned
    neneqd
    iffalsed
    #
    @5
    @7
    cL
    @2
    @5
    @1
    cB
    @5
    @1
    cB
    @5
    @13
    @14
    @15
    @17
    simp1d
    @5
    @13
    @14
    @15
    @17
    simp3d
    ltned
    neneqd
    iffalsed
    #
    eqtrd
    wph
    @0
    cr
    @1
    cF
    ditgeqiooicc.5
    ffvelrnda
    eqeltrd
    vx
    @10
    @9
    cr
    cG
    ditgeqiooicc.1
    fvmpt2
    syl2anc
    @18
    @19
    3eqtrrd
    itgeq2dv
    wph
    vx
    cA
    cB
    @2
    ditgeqiooicc.4
    ditgpos
    wph
    vx
    cA
    cB
    @3
    ditgeqiooicc.4
    ditgpos
    3eqtr4d
end
