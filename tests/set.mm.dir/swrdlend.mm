include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cfzo.mm"
include "cdm.mm"
include "wss.mm"
include "cc0.mm"
include "cmin.mm"
include "cv.mm"
include "caddc.mm"
include "cfv.mm"
include "cmpt.mm"
include "cif.mm"
include "swrdval.mm"
include "adantr.mm"
include "simpr.mm"
include "wb.mm"
include "3simpc.mm"
include "fzon.mm"
include "syl.mm"
include "mpbid.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "iftrued.mm"
include "fzo0n.mm"
include "biimpa.mm"
include "3adantl1.mm"
include "mpteq1d.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "3eqtrd.mm"
include "ex.mm"

theorem swrdlend
  let cF: class F
  let cL: class L
  let cV: class V
  let cW: class W
  let vi: setvar i


  assert |- ( ( W e. Word V /\ F e. ZZ /\ L e. ZZ ) -> ( L <_ F -> ( W substr <. F , L >. ) = (/) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cF
    cz
    wcel
    #
    cL
    cz
    wcel
    #
    w3a
    #
    cL
    cF
    cle
    wbr
    #
    cW
    cF
    cL
    cop
    csubstr
    co
    #
    c0
    wceq
    @4
    @5
    wa
    #
    @6
    cF
    cL
    cfzo
    co
    #
    cW
    cdm
    #
    wss
    #
    vi
    cc0
    cL
    cF
    cmin
    co
    cfzo
    co
    #
    vi
    cv
    cF
    caddc
    co
    cW
    cfv
    #
    cmpt
    #
    c0
    cif
    #
    @13
    c0
    @4
    @6
    @14
    wceq
    @5
    vi
    cW
    cF
    cL
    @0
    swrdval
    adantr
    @7
    @10
    @13
    c0
    @7
    @8
    c0
    @9
    @7
    @5
    @8
    c0
    wceq
    #
    @4
    @5
    simpr
    @7
    @2
    @3
    wa
    #
    @5
    @15
    wb
    @4
    @16
    @5
    @1
    @2
    @3
    3simpc
    adantr
    cF
    cL
    fzon
    syl
    mpbid
    @9
    0ss
    syl6eqss
    iftrued
    @7
    @13
    vi
    c0
    @12
    cmpt
    c0
    @7
    vi
    @11
    c0
    @12
    @2
    @3
    @5
    @11
    c0
    wceq
    #
    @1
    @16
    @5
    @17
    cF
    cL
    fzo0n
    biimpa
    3adantl1
    mpteq1d
    vi
    @12
    mpt0
    syl6eq
    3eqtrd
    ex
end
