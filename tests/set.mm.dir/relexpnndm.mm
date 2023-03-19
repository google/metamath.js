include "cn.mm"
include "wcel.mm"
include "crelexp.mm"
include "co.mm"
include "cdm.mm"
include "wss.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "dmeqd.mm"
include "sseq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "relexp1g.mm"
include "eqimss.mm"
include "syl.mm"
include "wa.mm"
include "ccom.mm"
include "relexpsucnnr.mm"
include "ancoms.mm"
include "dmcoss.mm"
include "syl6eqss.mm"
include "a1d.mm"
include "ex.mm"
include "a2d.mm"
include "nnind.mm"
include "imp.mm"

theorem relexpnndm
  let cR: class R
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vm: setvar m


  assert |- ( ( N e. NN /\ R e. V ) -> dom ( R ^r N ) C_ dom R )

  proof
    cN
    cn
    wcel
    cR
    cV
    wcel
    #
    cR
    cN
    crelexp
    co
    #
    cdm
    #
    cR
    cdm
    #
    wss
    #
    @0
    cR
    vn
    cv
    #
    crelexp
    co
    #
    cdm
    #
    @3
    wss
    #
    wi
    @0
    cR
    c1
    crelexp
    co
    #
    cdm
    #
    @3
    wss
    #
    wi
    @0
    cR
    vm
    cv
    #
    crelexp
    co
    #
    cdm
    #
    @3
    wss
    #
    wi
    @0
    cR
    @12
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cdm
    #
    @3
    wss
    #
    wi
    @0
    @4
    wi
    vn
    vm
    cN
    @5
    c1
    wceq
    #
    @8
    @11
    @0
    @20
    @7
    @10
    @3
    @20
    @6
    @9
    @5
    c1
    cR
    crelexp
    oveq2
    dmeqd
    sseq1d
    imbi2d
    vn
    vm
    weq
    #
    @8
    @15
    @0
    @21
    @7
    @14
    @3
    @21
    @6
    @13
    @5
    @12
    cR
    crelexp
    oveq2
    dmeqd
    sseq1d
    imbi2d
    @5
    @16
    wceq
    #
    @8
    @19
    @0
    @22
    @7
    @18
    @3
    @22
    @6
    @17
    @5
    @16
    cR
    crelexp
    oveq2
    dmeqd
    sseq1d
    imbi2d
    @5
    cN
    wceq
    #
    @8
    @4
    @0
    @23
    @7
    @2
    @3
    @23
    @6
    @1
    @5
    cN
    cR
    crelexp
    oveq2
    dmeqd
    sseq1d
    imbi2d
    @0
    @10
    @3
    wceq
    @11
    @0
    @9
    cR
    cR
    cV
    relexp1g
    dmeqd
    @10
    @3
    eqimss
    syl
    @12
    cn
    wcel
    #
    @0
    @15
    @19
    @24
    @0
    @15
    @19
    wi
    @24
    @0
    wa
    #
    @19
    @15
    @25
    @18
    @13
    cR
    ccom
    #
    cdm
    @3
    @25
    @17
    @26
    @0
    @24
    @17
    @26
    wceq
    cR
    @12
    cV
    relexpsucnnr
    ancoms
    dmeqd
    @13
    cR
    dmcoss
    syl6eqss
    a1d
    ex
    a2d
    nnind
    imp
end
