include "cv.mm"
include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cfv.mm"
include "cdit.mm"
include "cmin.mm"
include "wceq.mm"
include "cicc.mm"
include "wcel.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "ftc2ditglem.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "cvv.mm"
include "cioo.mm"
include "fvexd.mm"
include "cmpt.mm"
include "cibl.mm"
include "cc.mm"
include "ccncf.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "ditgswap.mm"
include "adantr.mm"
include "negeqd.mm"
include "ffvelrnd.mm"
include "negsubdi2d.mm"
include "3eqtrd.mm"
include "lecasei.mm"

theorem ftc2ditg
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let cY: class Y
  assume ftc2ditg.x: |- ( ph -> X e. RR )
  assume ftc2ditg.y: |- ( ph -> Y e. RR )
  assume ftc2ditg.a: |- ( ph -> A e. ( X [,] Y ) )
  assume ftc2ditg.b: |- ( ph -> B e. ( X [,] Y ) )
  assume ftc2ditg.c: |- ( ph -> ( RR _D F ) e. ( ( X (,) Y ) -cn-> CC ) )
  assume ftc2ditg.i: |- ( ph -> ( RR _D F ) e. L^1 )
  assume ftc2ditg.f: |- ( ph -> F e. ( ( X [,] Y ) -cn-> CC ) )

  disjoint A t
  disjoint B t
  disjoint F t
  disjoint ph t
  disjoint X t
  disjoint Y t
  assert |- ( ph -> S_ [ A -> B ] ( ( RR _D F ) ` t ) _d t = ( ( F ` B ) - ( F ` A ) ) )

  proof
    wph
    vt
    cA
    cB
    vt
    cv
    #
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cdit
    #
    cB
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    cmin
    co
    #
    wceq
    cA
    cB
    wph
    cX
    cY
    cicc
    co
    #
    cr
    cA
    wph
    cX
    cr
    wcel
    cY
    cr
    wcel
    @7
    cr
    wss
    ftc2ditg.x
    ftc2ditg.y
    cX
    cY
    iccssre
    syl2anc
    #
    ftc2ditg.a
    sseldd
    wph
    @7
    cr
    cB
    @8
    ftc2ditg.b
    sseldd
    wph
    vt
    cA
    cB
    cF
    cX
    cY
    ftc2ditg.x
    ftc2ditg.y
    ftc2ditg.a
    ftc2ditg.b
    ftc2ditg.c
    ftc2ditg.i
    ftc2ditg.f
    ftc2ditglem
    wph
    cB
    cA
    cle
    wbr
    #
    wa
    #
    @3
    vt
    cB
    cA
    @2
    cdit
    #
    cneg
    #
    @5
    @4
    cmin
    co
    #
    cneg
    #
    @6
    wph
    @3
    @12
    wceq
    @9
    wph
    vt
    cB
    cA
    @2
    cvv
    cX
    cY
    ftc2ditg.x
    ftc2ditg.y
    ftc2ditg.b
    ftc2ditg.a
    wph
    @0
    cX
    cY
    cioo
    co
    #
    wcel
    wa
    @0
    @1
    fvexd
    wph
    @1
    vt
    @15
    @2
    cmpt
    cibl
    wph
    vt
    @15
    cc
    @1
    wph
    @1
    @15
    cc
    ccncf
    co
    wcel
    @15
    cc
    @1
    wf
    ftc2ditg.c
    @15
    cc
    @1
    cncff
    syl
    feqmptd
    ftc2ditg.i
    eqeltrrd
    ditgswap
    adantr
    @10
    @11
    @13
    wph
    vt
    cB
    cA
    cF
    cX
    cY
    ftc2ditg.x
    ftc2ditg.y
    ftc2ditg.b
    ftc2ditg.a
    ftc2ditg.c
    ftc2ditg.i
    ftc2ditg.f
    ftc2ditglem
    negeqd
    wph
    @14
    @6
    wceq
    @9
    wph
    @5
    @4
    wph
    @7
    cc
    cA
    cF
    wph
    cF
    @7
    cc
    ccncf
    co
    wcel
    @7
    cc
    cF
    wf
    ftc2ditg.f
    @7
    cc
    cF
    cncff
    syl
    #
    ftc2ditg.a
    ffvelrnd
    wph
    @7
    cc
    cB
    cF
    @16
    ftc2ditg.b
    ffvelrnd
    negsubdi2d
    adantr
    3eqtrd
    lecasei
end
