include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wfun.mm"
include "cdm.mm"
include "wnel.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wb.mm"
include "wi.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "funsng.mm"
include "simpl.mm"
include "anim12ci.mm"
include "dmsnopg.mm"
include "adantl.mm"
include "ineq2d.mm"
include "wn.mm"
include "df-nel.mm"
include "disjsn.mm"
include "sylbb2.mm"
include "sylan9eq.mm"
include "jca.mm"
include "funun.mm"
include "syl.mm"
include "fsuppunbi.mm"
include "w3a.mm"
include "anim2i.mm"
include "ancomd.mm"
include "df-3an.mm"
include "sylibr.mm"
include "snopfsupp.mm"
include "biantrud.mm"
include "bitr4d.mm"
include "ex.mm"
include "relfsupp.mm"
include "brrelex2i.mm"
include "pm5.21ni.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem funsnfsupp
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( ( ( X e. V /\ Y e. W ) /\ ( Fun F /\ X e/ dom F ) ) -> ( ( F u. { <. X , Y >. } ) finSupp Z <-> F finSupp Z ) )

  proof
    cZ
    cvv
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cW
    wcel
    #
    wa
    #
    cF
    wfun
    #
    cX
    cF
    cdm
    #
    wnel
    #
    wa
    #
    wa
    #
    cF
    cX
    cY
    cop
    csn
    #
    cun
    #
    cZ
    cfsupp
    wbr
    #
    cF
    cZ
    cfsupp
    wbr
    #
    wb
    #
    wi
    @0
    @8
    @13
    @0
    @8
    wa
    #
    @11
    @12
    @9
    cZ
    cfsupp
    wbr
    #
    wa
    @12
    @14
    cF
    @9
    cZ
    @14
    @4
    @9
    wfun
    #
    wa
    #
    @5
    @9
    cdm
    #
    cin
    #
    c0
    wceq
    #
    wa
    #
    @10
    wfun
    @8
    @21
    @0
    @8
    @17
    @20
    @3
    @16
    @7
    @4
    cX
    cY
    cV
    cW
    funsng
    @4
    @6
    simpl
    anim12ci
    @3
    @7
    @19
    @5
    cX
    csn
    #
    cin
    #
    c0
    @3
    @18
    @22
    @5
    @2
    @18
    @22
    wceq
    @1
    cX
    cY
    cW
    dmsnopg
    adantl
    ineq2d
    @6
    @23
    c0
    wceq
    #
    @4
    @6
    cX
    @5
    wcel
    wn
    @24
    cX
    @5
    df-nel
    @5
    cX
    disjsn
    sylbb2
    adantl
    sylan9eq
    jca
    adantl
    cF
    @9
    funun
    syl
    fsuppunbi
    @14
    @15
    @12
    @14
    @1
    @2
    @0
    w3a
    #
    @15
    @14
    @3
    @0
    wa
    @25
    @14
    @0
    @3
    @8
    @3
    @0
    @3
    @7
    simpl
    anim2i
    ancomd
    @1
    @2
    @0
    df-3an
    sylibr
    cvv
    cV
    cW
    cX
    cY
    cZ
    snopfsupp
    syl
    biantrud
    bitr4d
    ex
    @0
    wn
    @13
    @8
    @11
    @0
    @12
    @10
    cZ
    cfsupp
    relfsupp
    brrelex2i
    cF
    cZ
    cfsupp
    relfsupp
    brrelex2i
    pm5.21ni
    a1d
    pm2.61i
end
