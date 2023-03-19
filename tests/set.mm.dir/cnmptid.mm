include "cv.mm"
include "cmpt.mm"
include "cid.mm"
include "cres.mm"
include "ccn.mm"
include "co.mm"
include "cvv.mm"
include "weq.mm"
include "copab.mm"
include "equcom.mm"
include "opabbii.mm"
include "dfid3.mm"
include "mptv.mm"
include "3eqtr4i.mm"
include "reseq1i.mm"
include "wss.mm"
include "wceq.mm"
include "ssv.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "idcn.mm"
include "syl.mm"
include "syl5eqelr.mm"

theorem cnmptid
  let wph: wff ph
  let vx: setvar x
  let cJ: class J
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  let cM: class M
  let cY: class Y
  let cZ: class Z
  let cK: class K
  let cL: class L
  let cP: class P
  assume cnmptid.j: |- ( ph -> J e. ( TopOn ` X ) )

  disjoint ph x
  disjoint J x
  disjoint X x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint D y
  disjoint D z
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J y
  disjoint x z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint P x
  disjoint P y
  assert |- ( ph -> ( x e. X |-> x ) e. ( J Cn J ) )

  proof
    wph
    vx
    cX
    vx
    cv
    #
    cmpt
    #
    cid
    cX
    cres
    #
    cJ
    cJ
    ccn
    co
    #
    @2
    vx
    cvv
    @0
    cmpt
    #
    cX
    cres
    #
    @1
    cid
    @4
    cX
    vx
    vy
    weq
    #
    vx
    vy
    copab
    vy
    vx
    weq
    #
    vx
    vy
    copab
    cid
    @4
    @6
    @7
    vx
    vy
    vx
    vy
    equcom
    opabbii
    vx
    vy
    dfid3
    vx
    vy
    @0
    mptv
    3eqtr4i
    reseq1i
    cX
    cvv
    wss
    @5
    @1
    wceq
    cX
    ssv
    vx
    cvv
    cX
    @0
    resmpt
    ax-mp
    eqtri
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    @2
    @3
    wcel
    cnmptid.j
    cJ
    cX
    idcn
    syl
    syl5eqelr
end
