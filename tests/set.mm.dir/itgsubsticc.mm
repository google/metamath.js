include "cicc.mm"
include "co.mm"
include "cmpt.mm"
include "cr.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "eqid.mm"
include "cle.mm"
include "w3a.mm"
include "eqidd.mm"
include "wceq.mm"
include "adantl.mm"
include "cxr.mm"
include "rexrd.mm"
include "ubicc2.mm"
include "syl3anc.mm"
include "fvmptd.mm"
include "ccncf.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp2d.mm"
include "itgsubsticclem.mm"

theorem itgsubsticc
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume itgsubsticc.1: |- ( ph -> X e. RR )
  assume itgsubsticc.2: |- ( ph -> Y e. RR )
  assume itgsubsticc.3: |- ( ph -> X <_ Y )
  assume itgsubsticc.4: |- ( ph -> ( x e. ( X [,] Y ) |-> A ) e. ( ( X [,] Y ) -cn-> ( K [,] L ) ) )
  assume itgsubsticc.5: |- ( ph -> ( u e. ( K [,] L ) |-> C ) e. ( ( K [,] L ) -cn-> CC ) )
  assume itgsubsticc.6: |- ( ph -> ( x e. ( X (,) Y ) |-> B ) e. ( ( ( X (,) Y ) -cn-> CC ) i^i L^1 ) )
  assume itgsubsticc.7: |- ( ph -> ( RR _D ( x e. ( X [,] Y ) |-> A ) ) = ( x e. ( X (,) Y ) |-> B ) )
  assume itgsubsticc.8: |- ( u = A -> C = E )
  assume itgsubsticc.9: |- ( x = X -> A = K )
  assume itgsubsticc.10: |- ( x = Y -> A = L )
  assume itgsubsticc.11: |- ( ph -> K e. RR )
  assume itgsubsticc.12: |- ( ph -> L e. RR )

  disjoint A u
  disjoint C x
  disjoint E u
  disjoint K u
  disjoint K x
  disjoint u x
  disjoint L u
  disjoint L x
  disjoint X u
  disjoint X x
  disjoint Y u
  disjoint Y x
  disjoint ph u
  disjoint ph x
  disjoint k x
  assert |- ( ph -> S_ [ K -> L ] C _d u = S_ [ X -> Y ] ( E x. B ) _d x )

  proof
    wph
    vx
    vu
    cA
    cB
    cC
    cE
    vu
    cK
    cL
    cicc
    co
    #
    cC
    cmpt
    #
    vu
    cr
    vu
    cv
    #
    @0
    wcel
    @2
    @1
    cfv
    @2
    cK
    clt
    wbr
    cK
    @1
    cfv
    cL
    @1
    cfv
    cif
    cif
    cmpt
    #
    cK
    cL
    cX
    cY
    @1
    eqid
    @3
    eqid
    itgsubsticc.1
    itgsubsticc.2
    itgsubsticc.3
    itgsubsticc.4
    itgsubsticc.6
    itgsubsticc.5
    itgsubsticc.11
    itgsubsticc.12
    wph
    cL
    cr
    wcel
    #
    cK
    cL
    cle
    wbr
    #
    cL
    cL
    cle
    wbr
    #
    wph
    cL
    @0
    wcel
    #
    @4
    @5
    @6
    w3a
    #
    wph
    cY
    vx
    cX
    cY
    cicc
    co
    #
    cA
    cmpt
    #
    cfv
    cL
    @0
    wph
    vx
    cY
    cA
    cL
    @9
    @10
    cr
    wph
    @10
    eqidd
    vx
    cv
    cY
    wceq
    cA
    cL
    wceq
    wph
    itgsubsticc.10
    adantl
    wph
    cX
    cxr
    wcel
    cY
    cxr
    wcel
    cX
    cY
    cle
    wbr
    cY
    @9
    wcel
    wph
    cX
    itgsubsticc.1
    rexrd
    wph
    cY
    itgsubsticc.2
    rexrd
    itgsubsticc.3
    cX
    cY
    ubicc2
    syl3anc
    #
    itgsubsticc.12
    fvmptd
    wph
    @9
    @0
    cY
    @10
    wph
    @10
    @9
    @0
    ccncf
    co
    wcel
    @9
    @0
    @10
    wf
    itgsubsticc.4
    @9
    @0
    @10
    cncff
    syl
    @11
    ffvelrnd
    eqeltrrd
    wph
    cK
    cr
    wcel
    @4
    @7
    @8
    wb
    itgsubsticc.11
    itgsubsticc.12
    cK
    cL
    cL
    elicc2
    syl2anc
    mpbid
    simp2d
    itgsubsticc.7
    itgsubsticc.8
    itgsubsticc.9
    itgsubsticc.10
    itgsubsticclem
end
