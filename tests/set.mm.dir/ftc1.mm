include "cfv.mm"
include "cr.mm"
include "cdv.mm"
include "co.mm"
include "wbr.mm"
include "cicc.mm"
include "cnt.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "cioo.mm"
include "ctop.mm"
include "wss.mm"
include "crn.mm"
include "ctg.mm"
include "crest.mm"
include "tgioo2.mm"
include "eqtr4i.mm"
include "retop.mm"
include "eqeltri.mm"
include "a1i.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "iooretop.mm"
include "eleqtrri.mm"
include "ioossicc.mm"
include "cuni.mm"
include "uniretop.mm"
include "unieqi.mm"
include "ssntr.mm"
include "syl22anc.mm"
include "sseldd.mm"
include "eqid.mm"
include "ftc1lem6.mm"
include "cc.mm"
include "ax-resscn.mm"
include "ftc1lem3.mm"
include "ftc1lem2.mm"
include "eldv.mm"
include "mpbir2and.mm"

theorem ftc1
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  let vr: setvar r
  let ve: setvar e
  let cX: class X
  let cE: class E
  let cH: class H
  let cY: class Y
  let cR: class R
  assume ftc1.g: |- G = ( x e. ( A [,] B ) |-> S. ( A (,) x ) ( F ` t ) _d t )
  assume ftc1.a: |- ( ph -> A e. RR )
  assume ftc1.b: |- ( ph -> B e. RR )
  assume ftc1.le: |- ( ph -> A <_ B )
  assume ftc1.s: |- ( ph -> ( A (,) B ) C_ D )
  assume ftc1.d: |- ( ph -> D C_ RR )
  assume ftc1.i: |- ( ph -> F e. L^1 )
  assume ftc1.c: |- ( ph -> C e. ( A (,) B ) )
  assume ftc1.f: |- ( ph -> F e. ( ( K CnP L ) ` C ) )
  assume ftc1.j: |- J = ( L |`t RR )
  assume ftc1.k: |- K = ( L |`t D )
  assume ftc1.l: |- L = ( TopOpen ` CCfld )

  disjoint t x
  disjoint C t
  disjoint C x
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
  disjoint L x
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
  disjoint L y
  disjoint L z
  disjoint R y
  assert |- ( ph -> C ( RR _D G ) ( F ` C ) )

  proof
    wph
    cC
    cC
    cF
    cfv
    #
    cr
    cG
    cdv
    co
    wbr
    cC
    cA
    cB
    cicc
    co
    #
    cJ
    cnt
    cfv
    cfv
    #
    wcel
    @0
    vz
    @1
    cC
    csn
    cdif
    vz
    cv
    #
    cG
    cfv
    cC
    cG
    cfv
    cmin
    co
    @3
    cC
    cmin
    co
    cdiv
    co
    cmpt
    #
    cC
    climc
    co
    wcel
    wph
    cA
    cB
    cioo
    co
    #
    @2
    cC
    wph
    cJ
    ctop
    wcel
    #
    @1
    cr
    wss
    #
    @5
    cJ
    wcel
    #
    @5
    @1
    wss
    #
    @5
    @2
    wss
    @6
    wph
    cJ
    cioo
    crn
    ctg
    cfv
    #
    ctop
    cJ
    cL
    cr
    crest
    co
    @10
    ftc1.j
    cL
    ftc1.l
    tgioo2
    eqtr4i
    #
    retop
    eqeltri
    a1i
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @7
    ftc1.a
    ftc1.b
    cA
    cB
    iccssre
    syl2anc
    #
    @8
    wph
    @5
    @10
    cJ
    cA
    cB
    iooretop
    @11
    eleqtrri
    a1i
    @9
    wph
    cA
    cB
    ioossicc
    a1i
    @1
    cJ
    @5
    cr
    cr
    @10
    cuni
    cJ
    cuni
    uniretop
    cJ
    @10
    @11
    unieqi
    eqtr4i
    ssntr
    syl22anc
    ftc1.c
    sseldd
    wph
    vx
    vz
    vt
    cA
    cB
    cC
    cD
    cF
    cG
    @4
    cJ
    cK
    cL
    ftc1.g
    ftc1.a
    ftc1.b
    ftc1.le
    ftc1.s
    ftc1.d
    ftc1.i
    ftc1.c
    ftc1.f
    ftc1.j
    ftc1.k
    ftc1.l
    @4
    eqid
    #
    ftc1lem6
    wph
    vz
    @1
    cC
    @0
    cr
    cJ
    cG
    @4
    cL
    ftc1.j
    ftc1.l
    @13
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    wph
    vx
    vt
    cA
    cB
    cD
    cF
    cG
    ftc1.g
    ftc1.a
    ftc1.b
    ftc1.le
    ftc1.s
    ftc1.d
    ftc1.i
    wph
    vx
    vt
    cA
    cB
    cC
    cD
    cF
    cG
    cJ
    cK
    cL
    ftc1.g
    ftc1.a
    ftc1.b
    ftc1.le
    ftc1.s
    ftc1.d
    ftc1.i
    ftc1.c
    ftc1.f
    ftc1.j
    ftc1.k
    ftc1.l
    ftc1lem3
    ftc1lem2
    @12
    eldv
    mpbir2and
end
