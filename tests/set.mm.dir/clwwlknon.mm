include "cvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cclwwlknon.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "eqeq2.mm"
include "rabbidv.mm"
include "oveq1.mm"
include "rabeqdv.mm"
include "clwwlknonmpt2.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "wral.mm"
include "cclwwlk.mm"
include "chash.mm"
include "isclwwlkn.mm"
include "cvv.mm"
include "cword.mm"
include "wne.mm"
include "w3a.mm"
include "eqid.mm"
include "clwwlkbp.mm"
include "fstwrdne.mm"
include "3adant1.mm"
include "syl.mm"
include "adantr.mm"
include "sylbi.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbid.mm"
include "clwwlknnn.mm"
include "nnnn0d.mm"
include "jca.mm"
include "ex.mm"
include "con3rr3.mm"
include "ralrimiv.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem clwwlknon
  let vw: setvar w
  let cG: class G
  let cN: class N
  let cX: class X
  let vg: setvar g
  let vn: setvar n
  let vv: setvar v

  disjoint G w
  disjoint N w
  disjoint X w
  disjoint G g
  disjoint G n
  disjoint G v
  disjoint g n
  disjoint g v
  disjoint g w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint X n
  disjoint X v
  assert |- ( X ( ClWWalksNOn ` G ) N ) = { w e. ( N ClWWalksN G ) | ( w ` 0 ) = X }

  proof
    cX
    cG
    cvtx
    cfv
    #
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cX
    cN
    cG
    cclwwlknon
    cfv
    #
    co
    #
    cc0
    vw
    cv
    #
    cfv
    #
    cX
    wceq
    #
    vw
    cN
    cG
    cclwwlkn
    co
    #
    crab
    #
    wceq
    vv
    vn
    cX
    cN
    @0
    cn0
    @7
    vv
    cv
    #
    wceq
    #
    vw
    vn
    cv
    #
    cG
    cclwwlkn
    co
    #
    crab
    #
    @10
    @4
    @8
    vw
    @14
    crab
    @11
    cX
    wceq
    @12
    @8
    vw
    @14
    @11
    cX
    @7
    eqeq2
    rabbidv
    @13
    cN
    wceq
    @8
    vw
    @14
    @9
    @13
    cN
    cG
    cclwwlkn
    oveq1
    rabeqdv
    vw
    vv
    vn
    cG
    clwwlknonmpt2
    #
    @8
    vw
    @9
    cN
    cG
    cclwwlkn
    ovex
    rabex
    ovmpt2
    @3
    wn
    #
    @5
    c0
    @10
    vv
    vn
    @15
    @4
    cX
    cN
    @0
    cn0
    @16
    mpt2ndm0
    @17
    @8
    wn
    #
    vw
    @9
    wral
    @10
    c0
    wceq
    @17
    @18
    vw
    @9
    @6
    @9
    wcel
    #
    @8
    @3
    @19
    @8
    @3
    @19
    @8
    wa
    #
    @1
    @2
    @20
    @7
    @0
    wcel
    #
    @1
    @19
    @21
    @8
    @19
    @6
    cG
    cclwwlk
    cfv
    wcel
    #
    @6
    chash
    cfv
    cN
    wceq
    #
    wa
    @21
    cG
    cN
    @6
    isclwwlkn
    @22
    @21
    @23
    @22
    cG
    cvv
    wcel
    #
    @6
    @0
    cword
    wcel
    #
    @6
    c0
    wne
    #
    w3a
    @21
    cG
    @0
    @6
    @0
    eqid
    clwwlkbp
    @25
    @26
    @21
    @24
    @0
    @6
    fstwrdne
    3adant1
    syl
    adantr
    sylbi
    adantr
    @8
    @21
    @1
    wb
    @19
    @7
    cX
    @0
    eleq1
    adantl
    mpbid
    @19
    @2
    @8
    @19
    cN
    cG
    cN
    @6
    clwwlknnn
    nnnn0d
    adantr
    jca
    ex
    con3rr3
    ralrimiv
    @8
    vw
    @9
    rabeq0
    sylibr
    eqtr4d
    pm2.61i
end
