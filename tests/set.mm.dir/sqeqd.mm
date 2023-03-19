include "wceq.mm"
include "wn.mm"
include "cneg.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wo.mm"
include "cc.mm"
include "wcel.mm"
include "wb.mm"
include "sqeqor.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "ord.mm"
include "wa.mm"
include "cre.mm"
include "cfv.mm"
include "cc0.mm"
include "simpl.mm"
include "fveq2.mm"
include "reneg.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "cle.mm"
include "wbr.mm"
include "adantr.mm"
include "breqtrd.mm"
include "cr.mm"
include "recl.mm"
include "le0neg1d.mm"
include "mpbird.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "negeqd.mm"
include "neg0.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "syl3anc.mm"
include "ex.mm"
include "syld.mm"
include "pm2.18d.mm"

theorem sqeqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume sqeqd.1: |- ( ph -> A e. CC )
  assume sqeqd.2: |- ( ph -> B e. CC )
  assume sqeqd.3: |- ( ph -> ( A ^ 2 ) = ( B ^ 2 ) )
  assume sqeqd.4: |- ( ph -> 0 <_ ( Re ` A ) )
  assume sqeqd.5: |- ( ph -> 0 <_ ( Re ` B ) )
  assume sqeqd.6: |- ( ( ph /\ ( Re ` A ) = 0 /\ ( Re ` B ) = 0 ) -> A = B )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cB
    wceq
    #
    wph
    @0
    wn
    cA
    cB
    cneg
    #
    wceq
    #
    @0
    wph
    @0
    @2
    wph
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    wceq
    #
    @0
    @2
    wo
    #
    sqeqd.3
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    #
    @3
    @4
    wb
    sqeqd.1
    sqeqd.2
    cA
    cB
    sqeqor
    syl2anc
    mpbid
    ord
    wph
    @2
    @0
    wph
    @2
    wa
    #
    wph
    cA
    cre
    cfv
    #
    cc0
    wceq
    cB
    cre
    cfv
    #
    cc0
    wceq
    #
    @0
    wph
    @2
    simpl
    @6
    @7
    @8
    cneg
    #
    cc0
    @2
    wph
    @7
    @1
    cre
    cfv
    #
    @10
    cA
    @1
    cre
    fveq2
    wph
    @5
    @11
    @10
    wceq
    sqeqd.2
    cB
    reneg
    syl
    sylan9eqr
    #
    @6
    @10
    cc0
    cneg
    cc0
    @6
    @8
    cc0
    @6
    @9
    @8
    cc0
    cle
    wbr
    #
    cc0
    @8
    cle
    wbr
    #
    @6
    @13
    cc0
    @10
    cle
    wbr
    @6
    cc0
    @7
    @10
    cle
    wph
    cc0
    @7
    cle
    wbr
    @2
    sqeqd.4
    adantr
    @12
    breqtrd
    @6
    @8
    @6
    @5
    @8
    cr
    wcel
    #
    wph
    @5
    @2
    sqeqd.2
    adantr
    cB
    recl
    syl
    #
    le0neg1d
    mpbird
    wph
    @14
    @2
    sqeqd.5
    adantr
    @6
    @15
    cc0
    cr
    wcel
    @9
    @13
    @14
    wa
    wb
    @16
    0re
    @8
    cc0
    letri3
    sylancl
    mpbir2and
    #
    negeqd
    neg0
    syl6eq
    eqtrd
    @17
    sqeqd.6
    syl3anc
    ex
    syld
    pm2.18d
end
