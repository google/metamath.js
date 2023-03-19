include "cxr.mm"
include "wcel.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "elixx1.mm"
include "3adant3.mm"
include "biimpa.mm"
include "simp3d.mm"
include "wi.mm"
include "simp1d.mm"
include "simp2.mm"
include "adantr.mm"
include "syl2anc.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "wss.mm"
include "ex.mm"
include "ssrdv.mm"
include "supxrleub.mm"
include "mpbird.mm"
include "wn.mm"
include "cq.mm"
include "wrex.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "qre.mm"
include "rexrd.mm"
include "ad2antlr.mm"
include "simp1.mm"
include "supxrcl.mm"
include "syl.mm"
include "wex.mm"
include "simp3.mm"
include "n0.mm"
include "sylib.mm"
include "simp2d.mm"
include "supxrub.mm"
include "sylan.mm"
include "xrletrd.mm"
include "exlimddv.mm"
include "xrlelttrd.mm"
include "simprr.mm"
include "mpbir3and.mm"
include "xrlenlt.mm"
include "mpbid.mm"
include "pm2.65da.mm"
include "nrexdv.mm"
include "qbtwnxr.mm"
include "3expia.mm"
include "mtod.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem ixxub
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
  assert |- ( ( A e. RR* /\ B e. RR* /\ ( A O B ) =/= (/) ) -> sup ( ( A O B ) , RR* , < ) = B )

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
    csup
    #
    cB
    wceq
    #
    @5
    cB
    cle
    wbr
    #
    cB
    @5
    cle
    wbr
    #
    @4
    @7
    vw
    cv
    #
    cB
    cle
    wbr
    #
    vw
    @2
    wral
    #
    @4
    @10
    vw
    @2
    @4
    @9
    @2
    wcel
    #
    wa
    #
    @9
    cB
    cS
    wbr
    #
    @10
    @13
    @9
    cxr
    wcel
    #
    cA
    @9
    cR
    wbr
    #
    @14
    @4
    @12
    @15
    @16
    @14
    w3a
    #
    @0
    @1
    @12
    @17
    wb
    #
    @3
    vx
    vy
    vz
    cA
    cB
    @9
    cR
    cS
    cO
    ixx.1
    elixx1
    3adant3
    #
    biimpa
    #
    simp3d
    @13
    @15
    @1
    @14
    @10
    wi
    @13
    @15
    @16
    @14
    @20
    simp1d
    #
    @4
    @1
    @12
    @0
    @1
    @3
    simp2
    #
    adantr
    ixxub.3
    syl2anc
    mpd
    ralrimiva
    @4
    @2
    cxr
    wss
    #
    @1
    @7
    @11
    wb
    @4
    vw
    @2
    cxr
    @4
    @12
    @15
    @21
    ex
    ssrdv
    #
    @22
    vw
    @2
    cB
    supxrleub
    syl2anc
    mpbird
    @4
    @8
    @5
    cB
    clt
    wbr
    #
    wn
    #
    @4
    @25
    @5
    @9
    clt
    wbr
    #
    @9
    cB
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
    @29
    vw
    cq
    @4
    @9
    cq
    wcel
    #
    wa
    #
    @29
    @27
    @32
    @27
    @28
    simprl
    #
    @32
    @29
    wa
    #
    @9
    @5
    cle
    wbr
    #
    @27
    wn
    #
    @34
    @23
    @12
    @35
    @4
    @23
    @31
    @29
    @24
    ad2antrr
    @34
    @12
    @15
    @16
    @14
    @31
    @15
    @4
    @29
    @31
    @9
    @9
    qre
    rexrd
    ad2antlr
    #
    @34
    cA
    @9
    clt
    wbr
    #
    @16
    @34
    cA
    @5
    @9
    @4
    @0
    @31
    @29
    @0
    @1
    @3
    simp1
    #
    ad2antrr
    #
    @4
    @5
    cxr
    wcel
    #
    @31
    @29
    @4
    @23
    @41
    @24
    @2
    supxrcl
    syl
    #
    ad2antrr
    #
    @37
    @4
    cA
    @5
    cle
    wbr
    #
    @31
    @29
    @4
    @12
    @44
    vw
    @4
    @3
    @12
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
    @13
    cA
    @9
    @5
    @4
    @0
    @12
    @39
    adantr
    #
    @21
    @4
    @41
    @12
    @42
    adantr
    @13
    @16
    cA
    @9
    cle
    wbr
    #
    @13
    @15
    @16
    @14
    @20
    simp2d
    @13
    @0
    @15
    @16
    @46
    wi
    @45
    @21
    ixxub.5
    syl2anc
    mpd
    @4
    @23
    @12
    @35
    @24
    @2
    @9
    supxrub
    #
    sylan
    xrletrd
    exlimddv
    ad2antrr
    @33
    xrlelttrd
    @34
    @0
    @15
    @38
    @16
    wi
    @40
    @37
    ixxub.4
    syl2anc
    mpd
    @34
    @28
    @14
    @32
    @27
    @28
    simprr
    @34
    @15
    @1
    @28
    @14
    wi
    @37
    @4
    @1
    @31
    @29
    @22
    ad2antrr
    ixxub.2
    syl2anc
    mpd
    @4
    @18
    @31
    @29
    @19
    ad2antrr
    mpbir3and
    @47
    syl2anc
    @34
    @15
    @41
    @35
    @36
    wb
    @37
    @43
    @9
    @5
    xrlenlt
    syl2anc
    mpbid
    pm2.65da
    nrexdv
    @4
    @41
    @1
    @25
    @30
    wi
    @42
    @22
    @41
    @1
    @25
    @30
    vw
    @5
    cB
    qbtwnxr
    3expia
    syl2anc
    mtod
    @4
    @1
    @41
    @8
    @26
    wb
    @22
    @42
    cB
    @5
    xrlenlt
    syl2anc
    mpbird
    @4
    @41
    @1
    @6
    @7
    @8
    wa
    wb
    @42
    @22
    @5
    cB
    xrletri3
    syl2anc
    mpbir2and
end
