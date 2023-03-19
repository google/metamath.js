include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "cq.mm"
include "cmap.mm"
include "wrex.mm"
include "wa.mm"
include "csn.mm"
include "0ex.mm"
include "snid.mm"
include "a1i.mm"
include "oveq2.mm"
include "cvv.mm"
include "qex.mm"
include "mapdm0.mm"
include "ax-mp.mm"
include "eqtr2d.mm"
include "adantl.mm"
include "eleqtrd.mm"
include "cr.mm"
include "cxmt.mm"
include "cxr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cme.mm"
include "cfn.mm"
include "rrxmetfi.mm"
include "syl.mm"
include "metxmet.mm"
include "adantr.mm"
include "reex.mm"
include "eqtrd.mm"
include "wb.mm"
include "elsng.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "eqeltrd.mm"
include "rpxrd.mm"
include "rpgt0d.mm"
include "jca.mm"
include "xblcntr.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "eleq1.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "crp.mm"
include "qndenserrnbllem.mm"
include "pm2.61dan.mm"

theorem qndenserrnbl
  let wph: wff ph
  let vy: setvar y
  let cD: class D
  let cE: class E
  let cI: class I
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume qndenserrnbl.i: |- ( ph -> I e. Fin )
  assume qndenserrnbl.x: |- ( ph -> X e. ( RR ^m I ) )
  assume qndenserrnbl.d: |- D = ( dist ` ( RR^ ` I ) )
  assume qndenserrnbl.e: |- ( ph -> E e. RR+ )

  disjoint D y
  disjoint E y
  disjoint I y
  disjoint X y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> E. y e. ( QQ ^m I ) y e. ( X ( ball ` D ) E ) )

  proof
    wph
    cI
    c0
    wceq
    #
    vy
    cv
    #
    cX
    cE
    cD
    cbl
    cfv
    #
    co
    #
    wcel
    #
    vy
    cq
    cI
    cmap
    co
    #
    wrex
    #
    wph
    @0
    wa
    #
    c0
    @5
    wcel
    c0
    @3
    wcel
    #
    @6
    @7
    c0
    c0
    csn
    #
    @5
    c0
    @9
    wcel
    @7
    c0
    0ex
    snid
    a1i
    @0
    @9
    @5
    wceq
    wph
    @0
    @5
    cq
    c0
    cmap
    co
    #
    @9
    cI
    c0
    cq
    cmap
    oveq2
    @10
    @9
    wceq
    #
    @0
    cq
    cvv
    wcel
    @11
    qex
    cq
    cvv
    mapdm0
    ax-mp
    a1i
    eqtr2d
    adantl
    eleqtrd
    @7
    c0
    c0
    cE
    @2
    co
    #
    @3
    @7
    cD
    cr
    cI
    cmap
    co
    #
    cxmt
    cfv
    wcel
    #
    c0
    @13
    wcel
    cE
    cxr
    wcel
    #
    cc0
    cE
    clt
    wbr
    #
    wa
    #
    c0
    @12
    wcel
    wph
    @14
    @0
    wph
    cD
    @13
    cme
    cfv
    wcel
    #
    @14
    wph
    cI
    cfn
    wcel
    #
    @18
    qndenserrnbl.i
    cD
    cI
    qndenserrnbl.d
    rrxmetfi
    syl
    cD
    @13
    metxmet
    syl
    adantr
    @7
    c0
    cX
    @13
    @7
    cX
    c0
    @7
    cX
    @9
    wcel
    #
    cX
    c0
    wceq
    #
    @7
    cX
    @13
    @9
    wph
    cX
    @13
    wcel
    #
    @0
    qndenserrnbl.x
    adantr
    #
    @0
    @13
    @9
    wceq
    wph
    @0
    @13
    cr
    c0
    cmap
    co
    #
    @9
    cI
    c0
    cr
    cmap
    oveq2
    @24
    @9
    wceq
    #
    @0
    cr
    cvv
    wcel
    @25
    reex
    cr
    cvv
    mapdm0
    ax-mp
    a1i
    eqtrd
    adantl
    eleqtrd
    wph
    @20
    @21
    wb
    #
    @0
    wph
    @22
    @26
    qndenserrnbl.x
    cX
    c0
    @13
    elsng
    syl
    adantr
    mpbid
    eqcomd
    #
    @23
    eqeltrd
    wph
    @17
    @0
    wph
    @15
    @16
    wph
    cE
    qndenserrnbl.e
    rpxrd
    wph
    cE
    qndenserrnbl.e
    rpgt0d
    jca
    adantr
    cD
    c0
    cE
    @13
    xblcntr
    syl3anc
    @7
    c0
    cX
    cE
    @2
    @27
    oveq1d
    eleqtrd
    @4
    @8
    vy
    c0
    @5
    @1
    c0
    @3
    eleq1
    rspcev
    syl2anc
    wph
    @0
    wn
    #
    wa
    vy
    cD
    cE
    cI
    cX
    wph
    @19
    @28
    qndenserrnbl.i
    adantr
    @28
    cI
    c0
    wne
    wph
    cI
    c0
    neqne
    adantl
    wph
    @22
    @28
    qndenserrnbl.x
    adantr
    qndenserrnbl.d
    wph
    cE
    crp
    wcel
    @28
    qndenserrnbl.e
    adantr
    qndenserrnbllem
    pm2.61dan
end
