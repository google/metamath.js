include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnp.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cflim.mm"
include "cflf.mm"
include "wi.mm"
include "cfil.mm"
include "wral.mm"
include "wa.mm"
include "cnpf2.mm"
include "3expa.mm"
include "3adantl3.mm"
include "cnpflfi.mm"
include "expcom.mm"
include "ralrimivw.mm"
include "adantl.mm"
include "jca.mm"
include "ex.mm"
include "csn.mm"
include "cnei.mm"
include "simpl1.mm"
include "simpl3.mm"
include "neiflim.mm"
include "syl2anc.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "snssd.mm"
include "snnzg.mm"
include "syl.mm"
include "neifil.mm"
include "syl3anc.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "fveq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpid.mm"
include "imdistanda.mm"
include "eqid.mm"
include "cnpflf2.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem cnpflf
  let cA: class A
  let vf: setvar f
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cL: class L

  disjoint A f
  disjoint X f
  disjoint Y f
  disjoint F f
  disjoint J f
  disjoint K f
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint L u
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X z
  disjoint Y u
  disjoint Y v
  disjoint Y x
  disjoint Y z
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint K y
  disjoint K z
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) /\ A e. X ) -> ( F e. ( ( J CnP K ) ` A ) <-> ( F : X --> Y /\ A. f e. ( Fil ` X ) ( A e. ( J fLim f ) -> ( F ` A ) e. ( ( K fLimf f ) ` F ) ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    w3a
    #
    cF
    cA
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cA
    cJ
    vf
    cv
    #
    cflim
    co
    #
    wcel
    #
    cA
    cF
    cfv
    #
    cF
    cK
    @6
    cflf
    co
    #
    cfv
    #
    wcel
    #
    wi
    #
    vf
    cX
    cfil
    cfv
    #
    wral
    #
    wa
    #
    @3
    @4
    @16
    @3
    @4
    wa
    @5
    @15
    @0
    @1
    @4
    @5
    @2
    @0
    @1
    @4
    @5
    cA
    cF
    cJ
    cK
    cX
    cY
    cnpf2
    3expa
    3adantl3
    @4
    @15
    @3
    @4
    @13
    vf
    @14
    @8
    @4
    @12
    cA
    cF
    cJ
    cK
    @6
    cnpflfi
    expcom
    ralrimivw
    adantl
    jca
    ex
    @3
    @16
    @5
    @9
    cF
    cK
    cA
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    cflf
    co
    #
    cfv
    #
    wcel
    #
    wa
    @4
    @3
    @5
    @15
    @21
    @3
    @5
    wa
    #
    @15
    cA
    cJ
    @18
    cflim
    co
    #
    wcel
    #
    @21
    @22
    @0
    @2
    @24
    @0
    @1
    @2
    @5
    simpl1
    #
    @0
    @1
    @2
    @5
    simpl3
    #
    cA
    cJ
    cX
    neiflim
    syl2anc
    @22
    @18
    @14
    wcel
    #
    @15
    @24
    @21
    wi
    #
    wi
    @22
    @0
    @17
    cX
    wss
    @17
    c0
    wne
    #
    @27
    @25
    @22
    cA
    cX
    @26
    snssd
    @22
    @2
    @29
    @26
    cA
    cX
    snnzg
    syl
    @17
    cJ
    cX
    neifil
    syl3anc
    @13
    @28
    vf
    @18
    @14
    @6
    @18
    wceq
    #
    @8
    @24
    @12
    @21
    @30
    @7
    @23
    cA
    @6
    @18
    cJ
    cflim
    oveq2
    eleq2d
    @30
    @11
    @20
    @9
    @30
    cF
    @10
    @19
    @6
    @18
    cK
    cflf
    oveq2
    fveq1d
    eleq2d
    imbi12d
    rspcv
    syl
    mpid
    imdistanda
    cA
    cF
    cJ
    cK
    @18
    cX
    cY
    @18
    eqid
    cnpflf2
    sylibrd
    impbid
end
