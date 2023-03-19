include "crcl.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "crelexp.mm"
include "co.mm"
include "c1.mm"
include "wo.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "wcel.mm"
include "wceq.mm"
include "w3a.mm"
include "brfvrcld.mm"
include "cid.mm"
include "cres.mm"
include "cvv.mm"
include "relexp0g.mm"
include "syl.mm"
include "breqd.mm"
include "wa.mm"
include "relres.mm"
include "releldmi.mm"
include "relelrni.mm"
include "dmresi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "rnresi.mm"
include "anim12i.mm"
include "syl2anc.mm"
include "resieq.mm"
include "biadan2.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "relexp1d.mm"
include "orbi12d.mm"
include "bitrd.mm"

theorem brfvrcld2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  assume brfvrcld2.r: |- ( ph -> R e. _V )


  assert |- ( ph -> ( A ( r* ` R ) B <-> ( ( A e. ( dom R u. ran R ) /\ B e. ( dom R u. ran R ) /\ A = B ) \/ A R B ) ) )

  proof
    wph
    cA
    cB
    cR
    crcl
    cfv
    wbr
    cA
    cB
    cR
    cc0
    crelexp
    co
    #
    wbr
    #
    cA
    cB
    cR
    c1
    crelexp
    co
    #
    wbr
    #
    wo
    cA
    cR
    cdm
    cR
    crn
    cun
    #
    wcel
    #
    cB
    @4
    wcel
    #
    cA
    cB
    wceq
    #
    w3a
    #
    cA
    cB
    cR
    wbr
    #
    wo
    wph
    cA
    cB
    cR
    brfvrcld2.r
    brfvrcld
    wph
    @1
    @8
    @3
    @9
    wph
    @1
    cA
    cB
    cid
    @4
    cres
    #
    wbr
    #
    @8
    wph
    @0
    @10
    cA
    cB
    wph
    cR
    cvv
    wcel
    @0
    @10
    wceq
    brfvrcld2.r
    cR
    cvv
    relexp0g
    syl
    breqd
    @11
    @5
    @6
    wa
    #
    @7
    wa
    @8
    @11
    @12
    @7
    @11
    cA
    @10
    cdm
    #
    wcel
    #
    cB
    @10
    crn
    #
    wcel
    #
    @12
    cA
    cB
    @10
    cid
    @4
    relres
    #
    releldmi
    cA
    cB
    @10
    @17
    relelrni
    @14
    @5
    @16
    @6
    @14
    @5
    @13
    @4
    cA
    @4
    dmresi
    eleq2i
    biimpi
    @16
    @6
    @15
    @4
    cB
    @4
    rnresi
    eleq2i
    biimpi
    anim12i
    syl2anc
    @4
    cA
    cB
    resieq
    biadan2
    @5
    @6
    @7
    df-3an
    bitr4i
    syl6bb
    wph
    @2
    cR
    cA
    cB
    wph
    cR
    brfvrcld2.r
    relexp1d
    breqd
    orbi12d
    bitrd
end
