include "wcel.mm"
include "w3a.mm"
include "cusgr.mm"
include "wne.mm"
include "ccplgr.mm"
include "cpr.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "wral.mm"
include "cupgr.mm"
include "wb.mm"
include "usgrupgr.mm"
include "cplgr3v.mm"
include "syl3an2.mm"
include "simp2.mm"
include "ctp.mm"
include "cvtx.mm"
include "cfv.mm"
include "eqtri.mm"
include "a1i.mm"
include "simp1.mm"
include "simp3.mm"
include "nb3grpr.mm"
include "bitrd.mm"

theorem cusgr3vnbpr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vn: setvar n
  let vv: setvar v
  assume cplgr3v.e: |- E = ( Edg ` G )
  assume cplgr3v.t: |- ( Vtx ` G ) = { A , B , C }
  assume cplgr3v.v: |- V = ( Vtx ` G )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint X y
  disjoint Y y
  disjoint Z y
  disjoint A n
  disjoint A v
  disjoint n v
  disjoint B n
  disjoint B v
  disjoint C n
  disjoint C v
  disjoint G n
  disjoint G v
  disjoint X n
  disjoint X v
  disjoint Y n
  disjoint Y v
  disjoint Z n
  disjoint Z v
  assert |- ( ( ( A e. X /\ B e. Y /\ C e. Z ) /\ G e. USGraph /\ ( A =/= B /\ A =/= C /\ B =/= C ) ) -> ( G e. ComplGraph <-> A. x e. V E. y e. V E. z e. ( V \ { y } ) ( G NeighbVtx x ) = { y , z } ) )

  proof
    cA
    cX
    wcel
    cB
    cY
    wcel
    cC
    cZ
    wcel
    w3a
    #
    cG
    cusgr
    wcel
    #
    cA
    cB
    wne
    cA
    cC
    wne
    cB
    cC
    wne
    w3a
    #
    w3a
    #
    cG
    ccplgr
    wcel
    #
    cA
    cB
    cpr
    cE
    wcel
    cB
    cC
    cpr
    cE
    wcel
    cC
    cA
    cpr
    cE
    wcel
    w3a
    #
    cG
    vx
    cv
    cnbgr
    co
    vy
    cv
    #
    vz
    cv
    cpr
    wceq
    vz
    cV
    @6
    csn
    cdif
    wrex
    vy
    cV
    wrex
    vx
    cV
    wral
    @1
    @0
    cG
    cupgr
    wcel
    @2
    @4
    @5
    wb
    cG
    usgrupgr
    cA
    cB
    cC
    cE
    cG
    cX
    cY
    cZ
    cplgr3v.e
    cplgr3v.t
    cplgr3v
    syl3an2
    @3
    vx
    vy
    vz
    cA
    cB
    cC
    cE
    cG
    cV
    cX
    cY
    cZ
    cplgr3v.v
    cplgr3v.e
    @0
    @1
    @2
    simp2
    cV
    cA
    cB
    cC
    ctp
    #
    wceq
    @3
    cV
    cG
    cvtx
    cfv
    @7
    cplgr3v.v
    cplgr3v.t
    eqtri
    a1i
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    nb3grpr
    bitrd
end
