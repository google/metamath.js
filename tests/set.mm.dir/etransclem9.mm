include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cdiv.mm"
include "cz.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "wne.mm"
include "wb.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mtbid.mm"
include "wa.mm"
include "cneg.mm"
include "cmin.mm"
include "df-neg.mm"
include "a1i.mm"
include "oveq1.mm"
include "eqcomd.mm"
include "adantl.mm"
include "zcnd.mm"
include "pncand.mm"
include "adantr.mm"
include "3eqtrrd.mm"
include "oveq1d.mm"
include "dvdsnegb.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "znegcld.mm"
include "eqeltrd.mm"
include "mtand.mm"
include "neqned.mm"

theorem etransclem9
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume etransclem9.k: |- ( ph -> K e. ZZ )
  assume etransclem9.kn0: |- ( ph -> K =/= 0 )
  assume etransclem9.m: |- ( ph -> M e. ZZ )
  assume etransclem9.n: |- ( ph -> N e. ZZ )
  assume etransclem9.km: |- ( ph -> -. K || M )
  assume etransclem9.kn: |- ( ph -> K || N )


  assert |- ( ph -> ( M + N ) =/= 0 )

  proof
    wph
    cM
    cN
    caddc
    co
    #
    cc0
    wph
    @0
    cc0
    wceq
    #
    cM
    cK
    cdiv
    co
    #
    cz
    wcel
    #
    wph
    cK
    cM
    cdvds
    wbr
    #
    @3
    etransclem9.km
    wph
    cK
    cz
    wcel
    #
    cK
    cc0
    wne
    #
    cM
    cz
    wcel
    @4
    @3
    wb
    etransclem9.k
    etransclem9.kn0
    etransclem9.m
    cK
    cM
    dvdsval2
    syl3anc
    mtbid
    wph
    @1
    wa
    #
    @2
    cN
    cneg
    #
    cK
    cdiv
    co
    #
    cz
    @7
    cM
    @8
    cK
    cdiv
    @7
    @8
    cc0
    cN
    cmin
    co
    #
    @0
    cN
    cmin
    co
    #
    cM
    @8
    @10
    wceq
    @7
    cN
    df-neg
    a1i
    @1
    @10
    @11
    wceq
    wph
    @1
    @11
    @10
    @0
    cc0
    cN
    cmin
    oveq1
    eqcomd
    adantl
    wph
    @11
    cM
    wceq
    @1
    wph
    cM
    cN
    wph
    cM
    etransclem9.m
    zcnd
    wph
    cN
    etransclem9.n
    zcnd
    pncand
    adantr
    3eqtrrd
    oveq1d
    wph
    @9
    cz
    wcel
    #
    @1
    wph
    cK
    @8
    cdvds
    wbr
    #
    @12
    wph
    cK
    cN
    cdvds
    wbr
    #
    @13
    etransclem9.kn
    wph
    @5
    cN
    cz
    wcel
    @14
    @13
    wb
    etransclem9.k
    etransclem9.n
    cK
    cN
    dvdsnegb
    syl2anc
    mpbid
    wph
    @5
    @6
    @8
    cz
    wcel
    @13
    @12
    wb
    etransclem9.k
    etransclem9.kn0
    wph
    cN
    etransclem9.n
    znegcld
    cK
    @8
    dvdsval2
    syl3anc
    mpbid
    adantr
    eqeltrd
    mtand
    neqned
end
