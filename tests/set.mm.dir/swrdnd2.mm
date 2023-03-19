include "cle.mm"
include "wbr.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "w3o.mm"
include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "3orass.mm"
include "wn.mm"
include "pm2.24.mm"
include "wa.mm"
include "cfzo.mm"
include "cdm.mm"
include "wss.mm"
include "cmin.mm"
include "cv.mm"
include "caddc.mm"
include "cmpt.mm"
include "cif.mm"
include "swrdval.mm"
include "ad2antrr.mm"
include "cn0.mm"
include "wf.mm"
include "wrdf.mm"
include "fdm.mm"
include "syl.mm"
include "lencl.mm"
include "3anass.mm"
include "ssfzoulel.mm"
include "imp.mm"
include "sylanbr.mm"
include "con3dimp.mm"
include "sseq2.mm"
include "notbid.mm"
include "syl5ibr.mm"
include "expd.mm"
include "exp4c.mm"
include "sylc.mm"
include "3impib.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "ex.mm"
include "expcom.mm"
include "com23.mm"
include "jaoi.mm"
include "swrdlend.mm"
include "com12.mm"
include "pm2.61d2.mm"
include "sylbi.mm"

theorem swrdnd2
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x


  assert |- ( ( W e. Word V /\ A e. ZZ /\ B e. ZZ ) -> ( ( B <_ A \/ ( # ` W ) <_ A \/ B <_ 0 ) -> ( W substr <. A , B >. ) = (/) ) )

  proof
    cB
    cA
    cle
    wbr
    #
    cW
    chash
    cfv
    #
    cA
    cle
    wbr
    #
    cB
    cc0
    cle
    wbr
    #
    w3o
    #
    cW
    cV
    cword
    #
    wcel
    #
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    w3a
    #
    cW
    cA
    cB
    cop
    csubstr
    co
    #
    c0
    wceq
    #
    @4
    @0
    @2
    @3
    wo
    #
    wo
    #
    @9
    @11
    wi
    #
    @0
    @2
    @3
    3orass
    @13
    @0
    @14
    @0
    @0
    wn
    #
    @14
    wi
    @12
    @0
    @14
    pm2.24
    @12
    @9
    @15
    @11
    @9
    @12
    @15
    @11
    wi
    @9
    @12
    wa
    #
    @15
    @11
    @16
    @15
    wa
    #
    @10
    cA
    cB
    cfzo
    co
    #
    cW
    cdm
    #
    wss
    #
    vx
    cc0
    cB
    cA
    cmin
    co
    cfzo
    co
    vx
    cv
    cA
    caddc
    co
    cW
    cfv
    cmpt
    #
    c0
    cif
    #
    c0
    @9
    @10
    @22
    wceq
    @12
    @15
    vx
    cW
    cA
    cB
    @5
    swrdval
    ad2antrr
    @17
    @20
    @21
    c0
    @16
    @15
    @20
    wn
    #
    @9
    @12
    @15
    @23
    wi
    #
    @6
    @7
    @8
    @12
    @24
    wi
    #
    @6
    @19
    cc0
    @1
    cfzo
    co
    #
    wceq
    #
    @1
    cn0
    wcel
    #
    @7
    @8
    wa
    #
    @25
    wi
    @6
    @26
    cV
    cW
    wf
    @27
    cV
    cW
    wrdf
    @26
    cV
    cW
    fdm
    syl
    cV
    cW
    lencl
    @27
    @28
    @29
    @12
    @24
    @27
    @28
    @29
    wa
    #
    @12
    wa
    #
    @15
    @23
    @31
    @15
    wa
    @23
    @27
    @18
    @26
    wss
    #
    wn
    @31
    @32
    @0
    @30
    @28
    @7
    @8
    w3a
    #
    @12
    @32
    @0
    wi
    #
    @28
    @7
    @8
    3anass
    @33
    @12
    @34
    cA
    cB
    @1
    ssfzoulel
    imp
    sylanbr
    con3dimp
    @27
    @20
    @32
    @19
    @26
    @18
    sseq2
    notbid
    syl5ibr
    expd
    exp4c
    sylc
    3impib
    imp
    imp
    iffalsed
    eqtrd
    ex
    expcom
    com23
    jaoi
    @9
    @0
    @11
    cA
    cB
    cV
    cW
    swrdlend
    com12
    pm2.61d2
    sylbi
    com12
end
