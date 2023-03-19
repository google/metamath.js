include "cvtxdg.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "cvtx.mm"
include "adantl.mm"
include "wcel.mm"
include "ciedg.mm"
include "cpr.mm"
include "cop.mm"
include "csn.mm"
include "preq2.mm"
include "eqcoms.mm"
include "dfsn2.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "eqtrd.mm"
include "cdif.mm"
include "wne.mm"
include "necomd.mm"
include "jca.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "1loopgrvd0.mm"
include "ex.mm"
include "cv.mm"
include "cedg.mm"
include "wrex.mm"
include "wn.mm"
include "wo.mm"
include "necom.mm"
include "df-ne.mm"
include "sylbb.mm"
include "syl.mm"
include "neneqd.mm"
include "ioran.mm"
include "crn.mm"
include "edgval.mm"
include "rneqd.mm"
include "rnsnopg.mm"
include "syl5eq.mm"
include "rexeqdv.mm"
include "cvv.mm"
include "wb.mm"
include "prex.mm"
include "eleq2.mm"
include "rexsng.mm"
include "mp1i.mm"
include "elprg.mm"
include "3bitrd.mm"
include "mtbird.mm"
include "cusgr.mm"
include "eqid.mm"
include "eleqtrrd.mm"
include "simpl.mm"
include "usgr1e.mm"
include "vtxdusgr0edgnel.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "pm2.61ine.mm"

theorem 1egrvtxdg0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let cV: class V
  let cX: class X
  let ve: setvar e
  assume 1egrvtxdg1.v: |- ( ph -> ( Vtx ` G ) = V )
  assume 1egrvtxdg1.a: |- ( ph -> A e. X )
  assume 1egrvtxdg1.b: |- ( ph -> B e. V )
  assume 1egrvtxdg1.c: |- ( ph -> C e. V )
  assume 1egrvtxdg1.n: |- ( ph -> B =/= C )
  assume 1egrvtxdg0.d: |- ( ph -> D e. V )
  assume 1egrvtxdg0.n: |- ( ph -> C =/= D )
  assume 1egrvtxdg0.i: |- ( ph -> ( iEdg ` G ) = { <. A , { B , D } >. } )


  assert |- ( ph -> ( ( VtxDeg ` G ) ` C ) = 0 )

  proof
    wph
    cC
    cG
    cvtxdg
    cfv
    #
    cfv
    cc0
    wceq
    #
    wi
    cB
    cD
    cB
    cD
    wceq
    #
    wph
    @1
    @2
    wph
    wa
    #
    cA
    cG
    cC
    cB
    cV
    cX
    wph
    cG
    cvtx
    cfv
    #
    cV
    wceq
    @2
    1egrvtxdg1.v
    adantl
    wph
    cA
    cX
    wcel
    #
    @2
    1egrvtxdg1.a
    adantl
    wph
    cB
    cV
    wcel
    @2
    1egrvtxdg1.b
    adantl
    @3
    cG
    ciedg
    cfv
    #
    cA
    cB
    cD
    cpr
    #
    cop
    #
    csn
    #
    cA
    cB
    csn
    #
    cop
    #
    csn
    wph
    @6
    @9
    wceq
    #
    @2
    1egrvtxdg0.i
    adantl
    @3
    @8
    @11
    @3
    @7
    @10
    cA
    @2
    @7
    @10
    wceq
    wph
    @2
    @7
    cB
    cB
    cpr
    #
    @10
    @7
    @13
    wceq
    cD
    cB
    cD
    cB
    cB
    preq2
    eqcoms
    cB
    dfsn2
    syl6eqr
    adantr
    opeq2d
    sneqd
    eqtrd
    wph
    cC
    cV
    @10
    cdif
    wcel
    #
    @2
    wph
    cC
    cV
    wcel
    #
    cC
    cB
    wne
    #
    wa
    @14
    wph
    @15
    @16
    1egrvtxdg1.c
    wph
    cB
    cC
    1egrvtxdg1.n
    necomd
    jca
    cC
    cV
    cB
    eldifsn
    sylibr
    adantl
    1loopgrvd0
    ex
    cB
    cD
    wne
    #
    wph
    @1
    @17
    wph
    wa
    #
    @1
    cC
    ve
    cv
    #
    wcel
    #
    ve
    cG
    cedg
    cfv
    #
    wrex
    #
    wn
    #
    @18
    @22
    cC
    cB
    wceq
    #
    cC
    cD
    wceq
    #
    wo
    #
    @18
    @24
    wn
    #
    @25
    wn
    #
    wa
    #
    @26
    wn
    wph
    @29
    @17
    wph
    @27
    @28
    wph
    cB
    cC
    wne
    #
    @27
    1egrvtxdg1.n
    @30
    @16
    @27
    cB
    cC
    necom
    cC
    cB
    df-ne
    sylbb
    syl
    wph
    cC
    cD
    1egrvtxdg0.n
    neneqd
    jca
    adantl
    @24
    @25
    ioran
    sylibr
    @18
    @22
    @20
    ve
    @7
    csn
    #
    wrex
    #
    cC
    @7
    wcel
    #
    @26
    @18
    @20
    ve
    @21
    @31
    wph
    @21
    @31
    wceq
    @17
    wph
    @21
    @6
    crn
    #
    @31
    cG
    edgval
    wph
    @34
    @9
    crn
    #
    @31
    wph
    @6
    @9
    1egrvtxdg0.i
    rneqd
    wph
    @5
    @35
    @31
    wceq
    1egrvtxdg1.a
    cA
    @7
    cX
    rnsnopg
    syl
    eqtrd
    syl5eq
    adantl
    rexeqdv
    @7
    cvv
    wcel
    @32
    @33
    wb
    @18
    cB
    cD
    prex
    @20
    @33
    ve
    @7
    cvv
    @19
    @7
    cC
    eleq2
    rexsng
    mp1i
    wph
    @33
    @26
    wb
    #
    @17
    wph
    @15
    @36
    1egrvtxdg1.c
    cC
    cB
    cD
    cV
    elprg
    syl
    adantl
    3bitrd
    mtbird
    @18
    cG
    cusgr
    wcel
    cC
    @4
    wcel
    #
    @1
    @23
    wb
    @18
    cA
    cB
    cD
    cG
    @4
    cX
    @4
    eqid
    #
    wph
    @5
    @17
    1egrvtxdg1.a
    adantl
    wph
    cB
    @4
    wcel
    @17
    wph
    cB
    cV
    @4
    1egrvtxdg1.b
    1egrvtxdg1.v
    eleqtrrd
    adantl
    wph
    cD
    @4
    wcel
    @17
    wph
    cD
    cV
    @4
    1egrvtxdg0.d
    1egrvtxdg1.v
    eleqtrrd
    adantl
    wph
    @12
    @17
    1egrvtxdg0.i
    adantl
    @17
    wph
    simpl
    usgr1e
    wph
    @37
    @17
    wph
    cC
    cV
    @4
    1egrvtxdg1.c
    1egrvtxdg1.v
    eleqtrrd
    adantl
    @0
    cC
    ve
    @21
    cG
    @4
    @38
    @21
    eqid
    @0
    eqid
    vtxdusgr0edgnel
    syl2anc
    mpbird
    ex
    pm2.61ine
end
