include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wi.mm"
include "ccnv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cnvun.mm"
include "imaeq1i.mm"
include "imaundir.mm"
include "eqtri.mm"
include "wceq.mm"
include "unexb.mm"
include "simpl.mm"
include "sylbir.mm"
include "suppimacnv.mm"
include "sylan.mm"
include "eqcomd.mm"
include "adantr.mm"
include "fsuppimpd.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "simpr.mm"
include "unfi.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "wb.mm"
include "eleq1d.mm"
include "mpbird.mm"
include "ex.mm"
include "wn.mm"
include "c0.mm"
include "supp0prc.mm"
include "0fin.mm"
include "syl6eqel.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem fsuppun
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cZ: class Z
  assume fsuppun.f: |- ( ph -> F finSupp Z )
  assume fsuppun.g: |- ( ph -> G finSupp Z )


  assert |- ( ph -> ( ( F u. G ) supp Z ) e. Fin )

  proof
    cF
    cG
    cun
    #
    cvv
    wcel
    #
    cZ
    cvv
    wcel
    #
    wa
    #
    wph
    @0
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    wi
    @3
    wph
    @5
    @3
    wph
    wa
    #
    @5
    @0
    ccnv
    #
    cvv
    cZ
    csn
    cdif
    #
    cima
    #
    cfn
    wcel
    #
    @6
    @9
    cF
    ccnv
    #
    @8
    cima
    #
    cG
    ccnv
    #
    @8
    cima
    #
    cun
    #
    cfn
    @9
    @11
    @13
    cun
    #
    @8
    cima
    @15
    @7
    @16
    @8
    cF
    cG
    cnvun
    imaeq1i
    @11
    @13
    @8
    imaundir
    eqtri
    @6
    @12
    cfn
    wcel
    @14
    cfn
    wcel
    @15
    cfn
    wcel
    @6
    @12
    cF
    cZ
    csupp
    co
    #
    cfn
    @3
    @12
    @17
    wceq
    wph
    @3
    @17
    @12
    @1
    cF
    cvv
    wcel
    #
    @2
    @17
    @12
    wceq
    @1
    @18
    cG
    cvv
    wcel
    #
    wa
    #
    @18
    cF
    cG
    unexb
    #
    @18
    @19
    simpl
    sylbir
    cF
    cvv
    cvv
    cZ
    suppimacnv
    sylan
    eqcomd
    adantr
    wph
    @17
    cfn
    wcel
    @3
    wph
    cF
    cZ
    fsuppun.f
    fsuppimpd
    adantl
    eqeltrd
    @6
    @14
    cG
    cZ
    csupp
    co
    #
    cfn
    @3
    @14
    @22
    wceq
    #
    wph
    @1
    @19
    @2
    @23
    @1
    @20
    @19
    @21
    @18
    @19
    simpr
    sylbir
    @19
    @2
    wa
    @22
    @14
    cG
    cvv
    cvv
    cZ
    suppimacnv
    eqcomd
    sylan
    adantr
    wph
    @22
    cfn
    wcel
    @3
    wph
    cG
    cZ
    fsuppun.g
    fsuppimpd
    adantl
    eqeltrd
    @12
    @14
    unfi
    syl2anc
    syl5eqel
    @3
    @5
    @10
    wb
    wph
    @3
    @4
    @9
    cfn
    @0
    cvv
    cvv
    cZ
    suppimacnv
    eleq1d
    adantr
    mpbird
    ex
    @3
    wn
    #
    @5
    wph
    @24
    @4
    c0
    cfn
    @0
    cZ
    supp0prc
    0fin
    syl6eqel
    a1d
    pm2.61i
end
