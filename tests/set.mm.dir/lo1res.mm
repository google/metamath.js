include "clo1.mm"
include "wcel.mm"
include "cres.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "cdm.mm"
include "cin.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wf.mm"
include "lo1f.mm"
include "lo1bdd.mm"
include "mpdan.mm"
include "wss.mm"
include "inss1.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "wceq.mm"
include "inss2.mm"
include "sseli.mm"
include "fvres.mm"
include "syl.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "ralbiia.mm"
include "sylibr.mm"
include "reximi.mm"
include "wb.mm"
include "fssres.mm"
include "sylancl.mm"
include "resres.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "reseq1d.mm"
include "syl5eqr.mm"
include "feq1d.mm"
include "mpbid.mm"
include "lo1dm.mm"
include "syl5ss.mm"
include "ello12.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem lo1res
  let cA: class A
  let cF: class F
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( F e. <_O(1) -> ( F |` A ) e. <_O(1) )

  proof
    cF
    clo1
    wcel
    #
    cF
    cA
    cres
    #
    clo1
    wcel
    #
    vx
    cv
    vy
    cv
    #
    cle
    wbr
    #
    @3
    @1
    cfv
    #
    vm
    cv
    #
    cle
    wbr
    #
    wi
    #
    vy
    cF
    cdm
    #
    cA
    cin
    #
    wral
    #
    vm
    cr
    wrex
    #
    vx
    cr
    wrex
    #
    @0
    @4
    @3
    cF
    cfv
    #
    @6
    cle
    wbr
    #
    wi
    #
    vy
    @9
    wral
    #
    vm
    cr
    wrex
    #
    vx
    cr
    wrex
    #
    @13
    @0
    @9
    cr
    cF
    wf
    #
    @19
    cF
    lo1f
    #
    vx
    vy
    @9
    vm
    cF
    lo1bdd
    mpdan
    @18
    @12
    vx
    cr
    @17
    @11
    vm
    cr
    @17
    @16
    vy
    @10
    wral
    #
    @11
    @10
    @9
    wss
    #
    @17
    @22
    wi
    @9
    cA
    inss1
    #
    @16
    vy
    @10
    @9
    ssralv
    ax-mp
    @8
    @16
    vy
    @10
    @3
    @10
    wcel
    #
    @7
    @15
    @4
    @25
    @5
    @14
    @6
    cle
    @25
    @3
    cA
    wcel
    @5
    @14
    wceq
    @10
    cA
    @3
    @9
    cA
    inss2
    sseli
    @3
    cA
    cF
    fvres
    syl
    breq1d
    imbi2d
    ralbiia
    sylibr
    reximi
    reximi
    syl
    @0
    @10
    cr
    @1
    wf
    #
    @10
    cr
    wss
    @2
    @13
    wb
    @0
    @10
    cr
    cF
    @10
    cres
    #
    wf
    #
    @26
    @0
    @20
    @23
    @28
    @21
    @24
    @9
    cr
    @10
    cF
    fssres
    sylancl
    @0
    @10
    cr
    @27
    @1
    @0
    @27
    cF
    @9
    cres
    #
    cA
    cres
    @1
    cF
    @9
    cA
    resres
    @0
    @29
    cF
    cA
    @0
    @20
    cF
    @9
    wfn
    @29
    cF
    wceq
    @21
    @9
    cr
    cF
    ffn
    @9
    cF
    fnresdm
    3syl
    reseq1d
    syl5eqr
    feq1d
    mpbid
    @0
    @10
    @9
    cr
    @24
    cF
    lo1dm
    syl5ss
    vx
    vy
    @10
    vm
    @1
    ello12
    syl2anc
    mpbird
end
