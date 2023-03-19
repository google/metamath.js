include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cdif.mm"
include "wcel.mm"
include "clt.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "wa.mm"
include "eldifi.mm"
include "adantl.mm"
include "wn.mm"
include "anim1i.mm"
include "rabid.mm"
include "sylibr.mm"
include "eldifn.mm"
include "adantr.mm"
include "pm2.65da.mm"
include "cxr.mm"
include "syldan.mm"
include "xrltnled.mm"
include "mpbird.mm"
include "jca.mm"
include "ex.mm"
include "simplbi.mm"
include "simprbi.mm"
include "mpbid.mm"
include "intnand.mm"
include "sylnibr.mm"
include "eldifd.mm"
include "impbid.mm"
include "alrimi.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfdif.mm"
include "dfcleqf.mm"

theorem preimagelt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume preimagelt.x: |- F/ x ph
  assume preimagelt.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume preimagelt.c: |- ( ph -> C e. RR* )

  disjoint A x
  disjoint k x
  assert |- ( ph -> ( A \ { x e. A | C <_ B } ) = { x e. A | B < C } )

  proof
    wph
    vx
    cv
    #
    cA
    cC
    cB
    cle
    wbr
    #
    vx
    cA
    crab
    #
    cdif
    #
    wcel
    #
    @0
    cB
    cC
    clt
    wbr
    #
    vx
    cA
    crab
    #
    wcel
    #
    wb
    #
    vx
    wal
    @3
    @6
    wceq
    wph
    @8
    vx
    preimagelt.x
    wph
    @4
    @7
    wph
    @4
    @7
    wph
    @4
    wa
    #
    @0
    cA
    wcel
    #
    @5
    wa
    @7
    @9
    @10
    @5
    @4
    @10
    wph
    @0
    cA
    @2
    eldifi
    #
    adantl
    #
    @9
    @5
    @1
    wn
    #
    @4
    @13
    wph
    @4
    @1
    @0
    @2
    wcel
    #
    @4
    @1
    wa
    @10
    @1
    wa
    #
    @14
    @4
    @10
    @1
    @11
    anim1i
    @1
    vx
    cA
    rabid
    #
    sylibr
    @4
    @14
    wn
    @1
    @0
    cA
    @2
    eldifn
    adantr
    pm2.65da
    adantl
    @9
    cB
    cC
    wph
    @4
    @10
    cB
    cxr
    wcel
    #
    @12
    preimagelt.b
    syldan
    wph
    cC
    cxr
    wcel
    #
    @4
    preimagelt.c
    adantr
    xrltnled
    mpbird
    jca
    @5
    vx
    cA
    rabid
    #
    sylibr
    ex
    wph
    @7
    @4
    wph
    @7
    wa
    #
    @0
    cA
    @2
    @7
    @10
    wph
    @7
    @10
    @5
    @19
    simplbi
    adantl
    #
    @20
    @15
    @14
    @20
    @1
    @10
    @20
    @5
    @13
    @7
    @5
    wph
    @7
    @10
    @5
    @19
    simprbi
    adantl
    @20
    cB
    cC
    wph
    @7
    @10
    @17
    @21
    preimagelt.b
    syldan
    wph
    @18
    @7
    preimagelt.c
    adantr
    xrltnled
    mpbid
    intnand
    @16
    sylnibr
    eldifd
    ex
    impbid
    alrimi
    vx
    @3
    @6
    vx
    cA
    @2
    vx
    cA
    nfcv
    @1
    vx
    cA
    nfrab1
    nfdif
    @5
    vx
    cA
    nfrab1
    dfcleqf
    sylibr
end
