include "ctop.mm"
include "wcel.mm"
include "cfil.mm"
include "cfv.mm"
include "wf.mm"
include "w3a.mm"
include "cflf.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "ctopon.mm"
include "wa.mm"
include "wb.mm"
include "toptopon.mm"
include "flfnei.mm"
include "syl3an1b.mm"
include "simplbda.mm"
include "3adant3.mm"
include "wi.mm"
include "wceq.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "3ad2ant3.mm"
include "mpd.mm"

theorem flfneii
  let cA: class A
  let cF: class F
  let cJ: class J
  let cL: class L
  let cN: class N
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vn: setvar n
  assume flfneii.x: |- X = U. J

  disjoint F s
  disjoint J s
  disjoint L s
  disjoint N s
  disjoint X s
  disjoint Y s
  disjoint n s
  disjoint F n
  disjoint A n
  disjoint J n
  disjoint L n
  disjoint N n
  disjoint X n
  disjoint Y n
  assert |- ( ( ( J e. Top /\ L e. ( Fil ` Y ) /\ F : Y --> X ) /\ A e. ( ( J fLimf L ) ` F ) /\ N e. ( ( nei ` J ) ` { A } ) ) -> E. s e. L ( F " s ) C_ N )

  proof
    cJ
    ctop
    wcel
    #
    cL
    cY
    cfil
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cA
    cF
    cJ
    cL
    cflf
    co
    cfv
    wcel
    #
    cN
    cA
    csn
    cJ
    cnei
    cfv
    cfv
    #
    wcel
    #
    w3a
    cF
    vs
    cv
    cima
    #
    vn
    cv
    #
    wss
    #
    vs
    cL
    wrex
    #
    vn
    @5
    wral
    #
    @7
    cN
    wss
    #
    vs
    cL
    wrex
    #
    @3
    @4
    @11
    @6
    @3
    @4
    cA
    cX
    wcel
    #
    @11
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    @1
    @2
    @4
    @14
    @11
    wa
    wb
    cJ
    cX
    flfneii.x
    toptopon
    cA
    vn
    cF
    cJ
    cL
    cX
    cY
    vs
    flfnei
    syl3an1b
    simplbda
    3adant3
    @6
    @3
    @11
    @13
    wi
    @4
    @10
    @13
    vn
    cN
    @5
    @8
    cN
    wceq
    @9
    @12
    vs
    cL
    @8
    cN
    @7
    sseq2
    rexbidv
    rspcv
    3ad2ant3
    mpd
end
