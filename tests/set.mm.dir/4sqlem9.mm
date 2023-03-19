include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cz.mm"
include "wcel.mm"
include "cmin.mm"
include "cc0.mm"
include "wceq.mm"
include "cc.mm"
include "wb.mm"
include "4sqlem5.mm"
include "simpld.mm"
include "zcnd.mm"
include "sqeq0.mm"
include "syl.mm"
include "biimpa.mm"
include "syldan.mm"
include "oveq2d.mm"
include "adantr.mm"
include "subid1d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "simprd.mm"
include "eqeltrrd.mm"
include "wne.mm"
include "nnzd.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "dvdssq.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem 4sqlem9
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cM: class M
  assume 4sqlem5.2: |- ( ph -> A e. ZZ )
  assume 4sqlem5.3: |- ( ph -> M e. NN )
  assume 4sqlem5.4: |- B = ( ( ( A + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sqlem9.5: |- ( ( ph /\ ps ) -> ( B ^ 2 ) = 0 )


  assert |- ( ( ph /\ ps ) -> ( M ^ 2 ) || ( A ^ 2 ) )

  proof
    wph
    wps
    wa
    #
    cM
    cA
    cdvds
    wbr
    #
    cM
    c2
    cexp
    co
    cA
    c2
    cexp
    co
    cdvds
    wbr
    #
    @0
    @1
    cA
    cM
    cdiv
    co
    #
    cz
    wcel
    #
    @0
    cA
    cB
    cmin
    co
    #
    cM
    cdiv
    co
    #
    @3
    cz
    @0
    @5
    cA
    cM
    cdiv
    @0
    @5
    cA
    cc0
    cmin
    co
    cA
    @0
    cB
    cc0
    cA
    cmin
    wph
    wps
    cB
    c2
    cexp
    co
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    4sqlem9.5
    wph
    @7
    @8
    wph
    cB
    cc
    wcel
    @7
    @8
    wb
    wph
    cB
    wph
    cB
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    wph
    cA
    cB
    cM
    4sqlem5.2
    4sqlem5.3
    4sqlem5.4
    4sqlem5
    #
    simpld
    zcnd
    cB
    sqeq0
    syl
    biimpa
    syldan
    oveq2d
    @0
    cA
    @0
    cA
    wph
    cA
    cz
    wcel
    #
    wps
    4sqlem5.2
    adantr
    #
    zcnd
    subid1d
    eqtrd
    oveq1d
    wph
    @10
    wps
    wph
    @9
    @10
    @11
    simprd
    adantr
    eqeltrrd
    wph
    @1
    @4
    wb
    #
    wps
    wph
    cM
    cz
    wcel
    #
    cM
    cc0
    wne
    @12
    @14
    wph
    cM
    4sqlem5.3
    nnzd
    #
    wph
    cM
    4sqlem5.3
    nnne0d
    4sqlem5.2
    cM
    cA
    dvdsval2
    syl3anc
    adantr
    mpbird
    @0
    @15
    @12
    @1
    @2
    wb
    wph
    @15
    wps
    @16
    adantr
    @13
    cM
    cA
    dvdssq
    syl2anc
    mpbid
end
