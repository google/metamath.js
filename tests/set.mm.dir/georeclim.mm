include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cli.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "wceq.mm"
include "cle.mm"
include "wn.mm"
include "0le1.mm"
include "0re.mm"
include "1re.mm"
include "lenlti.mm"
include "mpbi.mm"
include "fveq2.mm"
include "abs0.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "syl.mm"
include "reccld.mm"
include "1cnd.mm"
include "absdivd.mm"
include "abs1.mm"
include "oveq1i.mm"
include "absrpcld.mm"
include "recgt1d.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "geolim.mm"
include "divsubdird.mm"
include "dividd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cc.mm"
include "wcel.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancl.mm"
include "ltnri.mm"
include "wb.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "recdivd.mm"
include "eqtr3d.mm"
include "breqtrd.mm"

theorem georeclim
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  assume georeclim.1: |- ( ph -> A e. CC )
  assume georeclim.2: |- ( ph -> 1 < ( abs ` A ) )
  assume georeclim.3: |- ( ( ph /\ k e. NN0 ) -> ( F ` k ) = ( ( 1 / A ) ^ k ) )

  disjoint A k
  disjoint F k
  disjoint k ph
  assert |- ( ph -> seq 0 ( + , F ) ~~> ( A / ( A - 1 ) ) )

  proof
    wph
    caddc
    cF
    cc0
    cseq
    c1
    c1
    c1
    cA
    cdiv
    co
    #
    cmin
    co
    #
    cdiv
    co
    #
    cA
    cA
    c1
    cmin
    co
    #
    cdiv
    co
    #
    cli
    wph
    @0
    vk
    cF
    wph
    cA
    georeclim.1
    wph
    c1
    cA
    cabs
    cfv
    #
    clt
    wbr
    #
    cA
    cc0
    wne
    georeclim.2
    @6
    cA
    cc0
    cA
    cc0
    wceq
    #
    @6
    c1
    cc0
    clt
    wbr
    #
    cc0
    c1
    cle
    wbr
    @8
    wn
    0le1
    cc0
    c1
    0re
    1re
    lenlti
    mpbi
    @7
    @5
    cc0
    c1
    clt
    @7
    @5
    cc0
    cabs
    cfv
    cc0
    cA
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    breq2d
    mtbiri
    necon2ai
    syl
    #
    reccld
    wph
    @0
    cabs
    cfv
    #
    c1
    @5
    cdiv
    co
    #
    c1
    clt
    wph
    @10
    c1
    cabs
    cfv
    #
    @5
    cdiv
    co
    @11
    wph
    c1
    cA
    wph
    1cnd
    #
    georeclim.1
    @9
    absdivd
    @12
    c1
    @5
    cdiv
    abs1
    oveq1i
    syl6eq
    wph
    @6
    @11
    c1
    clt
    wbr
    georeclim.2
    wph
    @5
    wph
    cA
    georeclim.1
    @9
    absrpcld
    recgt1d
    mpbid
    eqbrtrd
    georeclim.3
    geolim
    wph
    c1
    @3
    cA
    cdiv
    co
    #
    cdiv
    co
    @2
    @4
    wph
    @14
    @1
    c1
    cdiv
    wph
    @14
    cA
    cA
    cdiv
    co
    #
    @0
    cmin
    co
    @1
    wph
    cA
    c1
    cA
    georeclim.1
    @13
    georeclim.1
    @9
    divsubdird
    wph
    @15
    c1
    @0
    cmin
    wph
    cA
    georeclim.1
    @9
    dividd
    oveq1d
    eqtrd
    oveq2d
    wph
    @3
    cA
    wph
    cA
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @3
    cc
    wcel
    georeclim.1
    ax-1cn
    cA
    c1
    subcl
    sylancl
    georeclim.1
    wph
    @3
    cc0
    wne
    cA
    c1
    wne
    #
    wph
    @6
    @18
    georeclim.2
    @6
    cA
    c1
    cA
    c1
    wceq
    #
    @6
    c1
    c1
    clt
    wbr
    c1
    1re
    ltnri
    @19
    @5
    c1
    c1
    clt
    @19
    @5
    @12
    c1
    cA
    c1
    cabs
    fveq2
    abs1
    syl6eq
    breq2d
    mtbiri
    necon2ai
    syl
    wph
    @3
    cc0
    cA
    c1
    wph
    @16
    @17
    @3
    cc0
    wceq
    @19
    wb
    georeclim.1
    ax-1cn
    cA
    c1
    subeq0
    sylancl
    necon3bid
    mpbird
    @9
    recdivd
    eqtr3d
    breqtrd
end
