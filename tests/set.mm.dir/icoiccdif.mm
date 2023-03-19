include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cico.mm"
include "co.mm"
include "cicc.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "wss.mm"
include "icossicc.mm"
include "a1i.mm"
include "sselda.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "cle.mm"
include "w3a.mm"
include "elico1.mm"
include "biimpa.mm"
include "simp1d.mm"
include "simplr.mm"
include "simp3d.mm"
include "xrltne.mm"
include "syl3anc.mm"
include "necomd.mm"
include "neneqd.mm"
include "velsn.mm"
include "sylnibr.mm"
include "eldifd.mm"
include "ex.mm"
include "ssrdv.mm"
include "simpll.mm"
include "eldifi.mm"
include "eliccxr.mm"
include "syl.mm"
include "adantl.mm"
include "wb.mm"
include "elicc1.mm"
include "adantr.mm"
include "mpbid.mm"
include "simp2d.mm"
include "eldifsni.mm"
include "xrleltne.mm"
include "mpbird.mm"
include "elicod.mm"
include "eqssd.mm"

theorem icoiccdif
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A [,) B ) = ( ( A [,] B ) \ { B } ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    cico
    co
    #
    cA
    cB
    cicc
    co
    #
    cB
    csn
    #
    cdif
    #
    @2
    vx
    @3
    @6
    @2
    vx
    cv
    #
    @3
    wcel
    #
    @7
    @6
    wcel
    #
    @2
    @8
    wa
    #
    @7
    @4
    @5
    @2
    @3
    @4
    @7
    @3
    @4
    wss
    @2
    cA
    cB
    icossicc
    a1i
    sselda
    @10
    @7
    cB
    wceq
    @7
    @5
    wcel
    @10
    @7
    cB
    @10
    cB
    @7
    @10
    @7
    cxr
    wcel
    #
    @1
    @7
    cB
    clt
    wbr
    #
    cB
    @7
    wne
    #
    @10
    @11
    cA
    @7
    cle
    wbr
    #
    @12
    @2
    @8
    @11
    @14
    @12
    w3a
    cA
    cB
    @7
    elico1
    biimpa
    #
    simp1d
    @0
    @1
    @8
    simplr
    @10
    @11
    @14
    @12
    @15
    simp3d
    @7
    cB
    xrltne
    syl3anc
    necomd
    neneqd
    vx
    cB
    velsn
    sylnibr
    eldifd
    ex
    ssrdv
    @2
    vx
    @6
    @3
    @2
    @9
    @8
    @2
    @9
    wa
    #
    cA
    cB
    @7
    @0
    @1
    @9
    simpll
    @0
    @1
    @9
    simplr
    #
    @9
    @11
    @2
    @9
    @7
    @4
    wcel
    #
    @11
    @7
    @4
    @5
    eldifi
    #
    @7
    cA
    cB
    eliccxr
    syl
    adantl
    #
    @16
    @11
    @14
    @7
    cB
    cle
    wbr
    #
    @16
    @18
    @11
    @14
    @21
    w3a
    #
    @9
    @18
    @2
    @19
    adantl
    @2
    @18
    @22
    wb
    @9
    cA
    cB
    @7
    elicc1
    adantr
    mpbid
    #
    simp2d
    @16
    @12
    @13
    @9
    @13
    @2
    @9
    @7
    cB
    @7
    @4
    cB
    eldifsni
    necomd
    adantl
    @16
    @11
    @1
    @21
    @12
    @13
    wb
    @20
    @17
    @16
    @11
    @14
    @21
    @23
    simp3d
    @7
    cB
    xrleltne
    syl3anc
    mpbird
    elicod
    ex
    ssrdv
    eqssd
end
