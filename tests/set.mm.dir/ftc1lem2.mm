include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cioo.mm"
include "cfv.mm"
include "citg.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "fvexd.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "cr.mm"
include "adantr.mm"
include "rexrd.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "simp3d.mm"
include "iooss2.mm"
include "sstrd.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "a1i.mm"
include "cmpt.mm"
include "cibl.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "iblss.mm"
include "itgcl.mm"
include "fmptd.mm"

theorem ftc1lem2
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  let cG: class G
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let vd: setvar d
  let vr: setvar r
  let ve: setvar e
  let cX: class X
  let cE: class E
  let cH: class H
  let cY: class Y
  let cL: class L
  let cR: class R
  assume ftc1.g: |- G = ( x e. ( A [,] B ) |-> S. ( A (,) x ) ( F ` t ) _d t )
  assume ftc1.a: |- ( ph -> A e. RR )
  assume ftc1.b: |- ( ph -> B e. RR )
  assume ftc1.le: |- ( ph -> A <_ B )
  assume ftc1.s: |- ( ph -> ( A (,) B ) C_ D )
  assume ftc1.d: |- ( ph -> D C_ RR )
  assume ftc1.i: |- ( ph -> F e. L^1 )
  assume ftc1a.f: |- ( ph -> F : D --> CC )

  disjoint t x
  disjoint D t
  disjoint D x
  disjoint A t
  disjoint A x
  disjoint B t
  disjoint B x
  disjoint ph t
  disjoint ph x
  disjoint F t
  disjoint F x
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint C t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint C u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint d r
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint D s
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint d e
  disjoint G d
  disjoint e r
  disjoint e s
  disjoint e u
  disjoint e y
  disjoint e z
  disjoint G e
  disjoint G r
  disjoint G s
  disjoint G u
  disjoint G y
  disjoint G z
  disjoint A d
  disjoint e t
  disjoint e v
  disjoint e w
  disjoint e x
  disjoint A e
  disjoint A r
  disjoint A s
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint B d
  disjoint B e
  disjoint B r
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint E t
  disjoint E y
  disjoint H s
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H y
  disjoint d ph
  disjoint e ph
  disjoint ph r
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint Y t
  disjoint Y x
  disjoint F d
  disjoint F r
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint L s
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint R y
  assert |- ( ph -> G : ( A [,] B ) --> CC )

  proof
    wph
    vx
    cA
    cB
    cicc
    co
    #
    vt
    cA
    vx
    cv
    #
    cioo
    co
    #
    vt
    cv
    #
    cF
    cfv
    #
    citg
    cc
    cG
    wph
    @1
    @0
    wcel
    #
    wa
    #
    vt
    @2
    @4
    cvv
    @6
    @3
    @2
    wcel
    wa
    @3
    cF
    fvexd
    @6
    vt
    @2
    cD
    @4
    cvv
    @6
    @2
    cA
    cB
    cioo
    co
    #
    cD
    @6
    cB
    cxr
    wcel
    @1
    cB
    cle
    wbr
    #
    @2
    @7
    wss
    @6
    cB
    wph
    cB
    cr
    wcel
    #
    @5
    ftc1.b
    adantr
    rexrd
    @6
    @1
    cr
    wcel
    #
    cA
    @1
    cle
    wbr
    #
    @8
    wph
    @5
    @10
    @11
    @8
    w3a
    #
    wph
    cA
    cr
    wcel
    @9
    @5
    @12
    wb
    ftc1.a
    ftc1.b
    cA
    cB
    @1
    elicc2
    syl2anc
    biimpa
    simp3d
    cA
    @1
    cB
    iooss2
    syl2anc
    wph
    @7
    cD
    wss
    @5
    ftc1.s
    adantr
    sstrd
    @2
    cvol
    cdm
    wcel
    @6
    cA
    @1
    ioombl
    a1i
    @6
    @3
    cD
    wcel
    wa
    @3
    cF
    fvexd
    wph
    vt
    cD
    @4
    cmpt
    #
    cibl
    wcel
    @5
    wph
    cF
    @13
    cibl
    wph
    vt
    cD
    cc
    cF
    ftc1a.f
    feqmptd
    ftc1.i
    eqeltrrd
    adantr
    iblss
    itgcl
    ftc1.g
    fmptd
end
