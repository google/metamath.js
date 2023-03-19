include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "crio.mm"
include "wa.mm"
include "wreu.mm"
include "lbreu.mm"
include "nfcv.mm"
include "nfriota1.mm"
include "nfbr.mm"
include "nfral.mm"
include "eqid.mm"
include "wceq.mm"
include "nfra1.mm"
include "nfriota.mm"
include "nfeq2.mm"
include "breq1.mm"
include "ralbid.mm"
include "riotaprop.mm"
include "syl.mm"
include "simprd.mm"
include "breq2.mm"
include "rspc.mm"
include "mpan9.mm"
include "3impa.mm"

theorem lble
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let vw: setvar w

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint A y
  disjoint w x
  disjoint w y
  disjoint S w
  disjoint A w
  assert |- ( ( S C_ RR /\ E. x e. S A. y e. S x <_ y /\ A e. S ) -> ( iota_ x e. S A. y e. S x <_ y ) <_ A )

  proof
    cS
    cr
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cS
    wral
    #
    vx
    cS
    wrex
    #
    cA
    cS
    wcel
    #
    @4
    vx
    cS
    crio
    #
    cA
    cle
    wbr
    #
    @0
    @5
    wa
    #
    @7
    @2
    cle
    wbr
    #
    vy
    cS
    wral
    #
    @6
    @8
    @9
    @7
    cS
    wcel
    #
    @11
    @9
    @4
    vx
    cS
    wreu
    @12
    @11
    wa
    vx
    vy
    cS
    lbreu
    @4
    @11
    vx
    cS
    @7
    @10
    vx
    vy
    cS
    vx
    cS
    nfcv
    vx
    @7
    @2
    cle
    @4
    vx
    cS
    nfriota1
    vx
    cle
    nfcv
    vx
    @2
    nfcv
    nfbr
    nfral
    @7
    eqid
    @1
    @7
    wceq
    @3
    @10
    vy
    cS
    vy
    @1
    @7
    @4
    vy
    vx
    cS
    @3
    vy
    cS
    nfra1
    vy
    cS
    nfcv
    nfriota
    #
    nfeq2
    @1
    @7
    @2
    cle
    breq1
    ralbid
    riotaprop
    syl
    simprd
    @10
    @8
    vy
    cA
    cS
    vy
    @7
    cA
    cle
    @13
    vy
    cle
    nfcv
    vy
    cA
    nfcv
    nfbr
    @2
    cA
    @7
    cle
    breq2
    rspc
    mpan9
    3impa
end
