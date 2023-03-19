include "cop.mm"
include "cxp.mm"
include "wcel.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "w3a.mm"
include "wi.mm"
include "opelxp.mm"
include "c0.mm"
include "wne.mm"
include "brne0.mm"
include "copab.mm"
include "wceq.mm"
include "3expb.mm"
include "breqd.mm"
include "brabv.mm"
include "anim2i.mm"
include "ex.mm"
include "adantr.mm"
include "sylbid.mm"
include "com23.mm"
include "a1d.mm"
include "wn.mm"
include "cmpt2.mm"
include "fvmptndm.mm"
include "df-ov.mm"
include "fveq1.mm"
include "syl5eq.mm"
include "0fv.mm"
include "syl6eq.mm"
include "eqneqall.mm"
include "3syl.mm"
include "pm2.61i.mm"
include "mpcom.mm"
include "com12.mm"
include "anc2ri.mm"
include "3anan32.mm"
include "syl6ibr.mm"
include "sylbi.mm"
include "imp.mm"

theorem bropfvvvvlem
  let wph: wff ph
  let wth: wff th
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let ve: setvar e
  let cE: class E
  let cO: class O
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume bropfvvvv.o: |- O = ( a e. U |-> ( b e. V , c e. W |-> { <. d , e >. | ph } ) )
  assume bropfvvvv.oo: |- ( ( A e. U /\ B e. S /\ C e. T ) -> ( B ( O ` A ) C ) = { <. d , e >. | th } )

  disjoint U a
  assert |- ( ( <. B , C >. e. ( S X. T ) /\ D ( B ( O ` A ) C ) E ) -> ( A e. U /\ ( B e. S /\ C e. T ) /\ ( D e. _V /\ E e. _V ) ) )

  proof
    cB
    cC
    cop
    #
    cS
    cT
    cxp
    wcel
    #
    cD
    cE
    cB
    cC
    cA
    cO
    cfv
    #
    co
    #
    wbr
    #
    cA
    cU
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cT
    wcel
    #
    wa
    #
    cD
    cvv
    wcel
    cE
    cvv
    wcel
    wa
    #
    w3a
    #
    @1
    @8
    @4
    @10
    wi
    cB
    cC
    cS
    cT
    opelxp
    @8
    @4
    @5
    @9
    wa
    #
    @8
    wa
    @10
    @8
    @4
    @11
    @4
    @8
    @11
    @3
    c0
    wne
    #
    @4
    @8
    @11
    wi
    #
    cD
    cE
    @3
    brne0
    @5
    @12
    @4
    @13
    wi
    #
    wi
    #
    @5
    @14
    @12
    @5
    @8
    @4
    @11
    @5
    @8
    @4
    @11
    wi
    @5
    @8
    wa
    #
    @4
    cD
    cE
    wth
    vd
    ve
    copab
    #
    wbr
    #
    @11
    @16
    @3
    @17
    cD
    cE
    @5
    @6
    @7
    @3
    @17
    wceq
    bropfvvvv.oo
    3expb
    breqd
    @5
    @18
    @11
    wi
    @8
    @5
    @18
    @11
    @18
    @9
    @5
    wth
    vd
    ve
    cD
    cE
    brabv
    anim2i
    ex
    adantr
    sylbid
    ex
    com23
    a1d
    @5
    wn
    @2
    c0
    wceq
    #
    @3
    c0
    wceq
    @15
    va
    cU
    vb
    vc
    cV
    cW
    wph
    vd
    ve
    copab
    cmpt2
    cO
    cA
    bropfvvvv.o
    fvmptndm
    @19
    @3
    @0
    c0
    cfv
    #
    c0
    @19
    @3
    @0
    @2
    cfv
    @20
    cB
    cC
    @2
    df-ov
    @0
    @2
    c0
    fveq1
    syl5eq
    @0
    0fv
    syl6eq
    @14
    @3
    c0
    eqneqall
    3syl
    pm2.61i
    mpcom
    com12
    anc2ri
    @5
    @8
    @9
    3anan32
    syl6ibr
    sylbi
    imp
end
