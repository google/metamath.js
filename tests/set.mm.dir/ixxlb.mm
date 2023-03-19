include "cxr.mm"
include "wcel.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "clt.mm"
include "cinf.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "wb.mm"
include "elixx1.mm"
include "3adant3.mm"
include "biimpa.mm"
include "simp1d.mm"
include "ex.mm"
include "ssrdv.mm"
include "infxrcl.mm"
include "syl.mm"
include "simp1.mm"
include "cq.mm"
include "wrex.mm"
include "simprr.mm"
include "cle.mm"
include "wn.mm"
include "ad2antrr.mm"
include "qre.mm"
include "rexrd.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "wi.mm"
include "syl2anc.mm"
include "mpd.mm"
include "simpll2.mm"
include "wex.mm"
include "simp3.mm"
include "n0.mm"
include "sylib.mm"
include "adantr.mm"
include "simpl2.mm"
include "infxrlb.mm"
include "sylan.mm"
include "simp3d.mm"
include "xrletrd.mm"
include "exlimddv.mm"
include "xrltletrd.mm"
include "mpbir3and.mm"
include "xrlenltd.mm"
include "mpbid.mm"
include "pm2.65da.mm"
include "nrexdv.mm"
include "qbtwnxr.mm"
include "3expia.mm"
include "mtod.mm"
include "xrnltled.mm"
include "wral.mm"
include "simp2d.mm"
include "ralrimiva.mm"
include "infxrgelb.mm"
include "mpbird.mm"
include "xrletrid.mm"

theorem ixxlb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cO: class O
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cP: class P
  let cT: class T
  let cU: class U
  let cW: class W
  let cX: class X
  assume ixx.1: |- O = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x R z /\ z S y ) } )
  assume ixxub.2: |- ( ( w e. RR* /\ B e. RR* ) -> ( w < B -> w S B ) )
  assume ixxub.3: |- ( ( w e. RR* /\ B e. RR* ) -> ( w S B -> w <_ B ) )
  assume ixxub.4: |- ( ( A e. RR* /\ w e. RR* ) -> ( A < w -> A R w ) )
  assume ixxub.5: |- ( ( A e. RR* /\ w e. RR* ) -> ( A R w -> A <_ w ) )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint O w
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint Q w
  disjoint P w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint W w
  disjoint X w
  assert |- ( ( A e. RR* /\ B e. RR* /\ ( A O B ) =/= (/) ) -> inf ( ( A O B ) , RR* , < ) = A )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cO
    co
    #
    c0
    wne
    #
    w3a
    #
    @2
    cxr
    clt
    cinf
    #
    cA
    @4
    @2
    cxr
    wss
    #
    @5
    cxr
    wcel
    #
    @4
    vw
    @2
    cxr
    @4
    vw
    cv
    #
    @2
    wcel
    #
    @8
    cxr
    wcel
    #
    @4
    @9
    wa
    #
    @10
    cA
    @8
    cR
    wbr
    #
    @8
    cB
    cS
    wbr
    #
    @4
    @9
    @10
    @12
    @13
    w3a
    #
    @0
    @1
    @9
    @14
    wb
    #
    @3
    vx
    vy
    vz
    cA
    cB
    @8
    cR
    cS
    cO
    ixx.1
    elixx1
    3adant3
    #
    biimpa
    #
    simp1d
    #
    ex
    ssrdv
    #
    @2
    infxrcl
    syl
    #
    @0
    @1
    @3
    simp1
    #
    @4
    @5
    cA
    @20
    @21
    @4
    cA
    @5
    clt
    wbr
    #
    cA
    @8
    clt
    wbr
    #
    @8
    @5
    clt
    wbr
    #
    wa
    #
    vw
    cq
    wrex
    #
    @4
    @25
    vw
    cq
    @4
    @8
    cq
    wcel
    #
    wa
    #
    @25
    @24
    @28
    @23
    @24
    simprr
    #
    @28
    @25
    wa
    #
    @5
    @8
    cle
    wbr
    #
    @24
    wn
    @30
    @6
    @9
    @31
    @4
    @6
    @27
    @25
    @19
    ad2antrr
    @30
    @9
    @10
    @12
    @13
    @27
    @10
    @4
    @25
    @27
    @8
    @8
    qre
    rexrd
    ad2antlr
    #
    @30
    @23
    @12
    @28
    @23
    @24
    simprl
    @30
    @0
    @10
    @23
    @12
    wi
    @4
    @0
    @27
    @25
    @21
    ad2antrr
    @32
    ixxub.4
    syl2anc
    mpd
    @30
    @8
    cB
    clt
    wbr
    #
    @13
    @30
    @8
    @5
    cB
    @32
    @4
    @7
    @27
    @25
    @20
    ad2antrr
    #
    @0
    @1
    @3
    @27
    @25
    simpll2
    #
    @29
    @4
    @5
    cB
    cle
    wbr
    #
    @27
    @25
    @4
    @9
    @36
    vw
    @4
    @3
    @9
    vw
    wex
    @0
    @1
    @3
    simp3
    vw
    @2
    n0
    sylib
    @11
    @5
    @8
    cB
    @4
    @7
    @9
    @20
    adantr
    @18
    @0
    @1
    @3
    @9
    simpl2
    #
    @4
    @6
    @9
    @31
    @19
    @2
    @8
    infxrlb
    #
    sylan
    @11
    @13
    @8
    cB
    cle
    wbr
    #
    @11
    @10
    @12
    @13
    @17
    simp3d
    @11
    @10
    @1
    @13
    @39
    wi
    @18
    @37
    ixxub.3
    syl2anc
    mpd
    xrletrd
    exlimddv
    ad2antrr
    xrltletrd
    @30
    @10
    @1
    @33
    @13
    wi
    @32
    @35
    ixxub.2
    syl2anc
    mpd
    @4
    @15
    @27
    @25
    @16
    ad2antrr
    mpbir3and
    @38
    syl2anc
    @30
    @5
    @8
    @34
    @32
    xrlenltd
    mpbid
    pm2.65da
    nrexdv
    @4
    @0
    @7
    @22
    @26
    wi
    @21
    @20
    @0
    @7
    @22
    @26
    vw
    cA
    @5
    qbtwnxr
    3expia
    syl2anc
    mtod
    xrnltled
    @4
    cA
    @5
    cle
    wbr
    #
    cA
    @8
    cle
    wbr
    #
    vw
    @2
    wral
    #
    @4
    @41
    vw
    @2
    @11
    @12
    @41
    @11
    @10
    @12
    @13
    @17
    simp2d
    @11
    @0
    @10
    @12
    @41
    wi
    @4
    @0
    @9
    @21
    adantr
    @18
    ixxub.5
    syl2anc
    mpd
    ralrimiva
    @4
    @6
    @0
    @40
    @42
    wb
    @19
    @21
    vw
    @2
    cA
    infxrgelb
    syl2anc
    mpbird
    xrletrid
end
