include "cfz.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "0fin.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "wne.mm"
include "cuz.mm"
include "cfv.mm"
include "fzn0.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "ccnv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "cin.mm"
include "onfin2.mm"
include "inss2.mm"
include "eqsstri.mm"
include "cn0.mm"
include "wf1o.mm"
include "eqid.mm"
include "hashgf1o.mm"
include "peano2uz.mm"
include "uznn0sub.mm"
include "syl.mm"
include "f1ocnvdm.mm"
include "sylancr.mm"
include "sseldi.mm"
include "fzen2.mm"
include "enfii.mm"
include "syl2anc.mm"
include "sylbi.mm"
include "pm2.61ine.mm"

theorem fzfi
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( M ... N ) e. Fin

  proof
    cM
    cN
    cfz
    co
    #
    cfn
    wcel
    #
    @0
    c0
    @0
    c0
    wceq
    @1
    c0
    cfn
    wcel
    0fin
    @0
    c0
    cfn
    eleq1
    mpbiri
    @0
    c0
    wne
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    cM
    cN
    fzn0
    @3
    cN
    c1
    caddc
    co
    #
    cM
    cmin
    co
    #
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    cc0
    crdg
    com
    cres
    #
    ccnv
    cfv
    #
    cfn
    wcel
    @0
    @7
    cen
    wbr
    @1
    @3
    com
    cfn
    @7
    com
    con0
    cfn
    cin
    cfn
    onfin2
    con0
    cfn
    inss2
    eqsstri
    @3
    com
    cn0
    @6
    wf1o
    @5
    cn0
    wcel
    #
    @7
    com
    wcel
    vx
    @6
    @6
    eqid
    #
    hashgf1o
    @3
    @4
    @2
    wcel
    @8
    cM
    cN
    peano2uz
    cM
    @4
    uznn0sub
    syl
    com
    cn0
    @5
    @6
    f1ocnvdm
    sylancr
    sseldi
    vx
    @6
    cM
    cN
    @9
    fzen2
    @0
    @7
    enfii
    syl2anc
    sylbi
    pm2.61ine
end
