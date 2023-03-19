include "wcel.mm"
include "cres.mm"
include "wi.mm"
include "wf1o.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "symgfixelq.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "wf1.mm"
include "wss.mm"
include "f1of1.mm"
include "ad2antrl.mm"
include "difssd.mm"
include "f1ores.mm"
include "syl2anc.mm"
include "reseq2i.mm"
include "a1i.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foima.mm"
include "eqcomd.mm"
include "syl.mm"
include "sneq.mm"
include "eqcoms.mm"
include "ad2antll.mm"
include "wfn.mm"
include "f1ofn.mm"
include "simpl.mm"
include "fnsnfv.mm"
include "eqtrd.mm"
include "difeq12d.mm"
include "ccnv.mm"
include "wfun.mm"
include "crn.mm"
include "dff1o2.mm"
include "simp2bi.mm"
include "imadif.mm"
include "3eqtr4d.mm"
include "f1oeq123d.mm"
include "mpbird.mm"
include "ancoms.mm"
include "symgfixels.mm"
include "syl5ibr.mm"
include "expd.mm"
include "sylbid.mm"
include "pm2.43i.mm"
include "impcom.mm"

theorem symgfixelsi
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cK: class K
  let cN: class N
  let vq: setvar q
  assume symgfixf.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume symgfixf.q: |- Q = { q e. P | ( q ` K ) = K }
  assume symgfixf.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgfixf.d: |- D = ( N \ { K } )

  disjoint K q
  disjoint P q
  assert |- ( ( K e. N /\ F e. Q ) -> ( F |` D ) e. S )

  proof
    cF
    cQ
    wcel
    #
    cK
    cN
    wcel
    #
    cF
    cD
    cres
    #
    cS
    wcel
    #
    @0
    @1
    @3
    wi
    #
    @0
    @0
    cN
    cN
    cF
    wf1o
    #
    cK
    cF
    cfv
    #
    cK
    wceq
    #
    wa
    #
    @4
    cP
    cQ
    cF
    cK
    cN
    cQ
    vq
    symgfixf.p
    symgfixf.q
    symgfixelq
    @0
    @8
    @1
    @3
    @8
    @1
    wa
    @3
    @0
    cD
    cD
    @2
    wf1o
    #
    @1
    @8
    @9
    @1
    @8
    wa
    #
    @9
    cN
    cK
    csn
    #
    cdif
    #
    cF
    @12
    cima
    #
    cF
    @12
    cres
    #
    wf1o
    #
    @10
    cN
    cN
    cF
    wf1
    #
    @12
    cN
    wss
    @15
    @5
    @16
    @1
    @7
    cN
    cN
    cF
    f1of1
    ad2antrl
    @10
    cN
    @11
    difssd
    cN
    cN
    @12
    cF
    f1ores
    syl2anc
    @10
    cD
    @12
    cD
    @13
    @2
    @14
    @2
    @14
    wceq
    @10
    cD
    @12
    cF
    symgfixf.d
    reseq2i
    a1i
    cD
    @12
    wceq
    @10
    symgfixf.d
    a1i
    #
    @10
    @12
    cF
    cN
    cima
    #
    cF
    @11
    cima
    #
    cdif
    #
    cD
    @13
    @10
    cN
    @18
    @11
    @19
    @5
    cN
    @18
    wceq
    #
    @1
    @7
    @5
    cN
    cN
    cF
    wfo
    #
    @21
    cN
    cN
    cF
    f1ofo
    @22
    @18
    cN
    cN
    cN
    cF
    foima
    eqcomd
    syl
    ad2antrl
    @10
    @11
    @6
    csn
    #
    @19
    @7
    @11
    @23
    wceq
    #
    @1
    @5
    @24
    cK
    @6
    cK
    @6
    sneq
    eqcoms
    ad2antll
    @10
    cF
    cN
    wfn
    #
    @1
    @23
    @19
    wceq
    @5
    @25
    @1
    @7
    cN
    cN
    cF
    f1ofn
    ad2antrl
    @1
    @8
    simpl
    cN
    cK
    cF
    fnsnfv
    syl2anc
    eqtrd
    difeq12d
    @17
    @10
    cF
    ccnv
    wfun
    #
    @13
    @20
    wceq
    @5
    @26
    @1
    @7
    @5
    @25
    @26
    cF
    crn
    cN
    wceq
    cN
    cN
    cF
    dff1o2
    simp2bi
    ad2antrl
    cN
    @11
    cF
    imadif
    syl
    3eqtr4d
    f1oeq123d
    mpbird
    ancoms
    cD
    cP
    cQ
    cS
    cF
    cK
    cN
    cQ
    vq
    symgfixf.p
    symgfixf.q
    symgfixf.s
    symgfixf.d
    symgfixels
    syl5ibr
    expd
    sylbid
    pm2.43i
    impcom
end
