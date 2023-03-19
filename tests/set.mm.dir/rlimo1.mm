include "crli.mm"
include "wbr.mm"
include "co1.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "cfv.mm"
include "cabs.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cmin.mm"
include "co.mm"
include "c1.mm"
include "clt.mm"
include "cc.mm"
include "rlimf.mm"
include "ffvelrnda.mm"
include "ralrimiva.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "cmpt.mm"
include "feqmptd.mm"
include "id.mm"
include "eqbrtrrd.mm"
include "rlimi.mm"
include "wa.mm"
include "caddc.mm"
include "rlimcl.mm"
include "adantr.mm"
include "abscld.mm"
include "peano2re.mm"
include "syl.mm"
include "adantlr.mm"
include "abs2difd.mm"
include "resubcld.mm"
include "subcld.mm"
include "1red.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "ltsubadd2d.mm"
include "sylibd.mm"
include "ltle.mm"
include "syl2anc.mm"
include "syld.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "reximdva.mm"
include "mpd.mm"
include "wf.mm"
include "wss.mm"
include "wb.mm"
include "rlimss.mm"
include "elo12.mm"
include "mpbird.mm"

theorem rlimo1
  let cA: class A
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let cG: class G


  assert |- ( F ~~>r A -> F e. O(1) )

  proof
    cF
    cA
    crli
    wbr
    #
    cF
    co1
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    @3
    cF
    cfv
    #
    cabs
    cfv
    #
    vw
    cv
    #
    cle
    wbr
    #
    wi
    #
    vz
    cF
    cdm
    #
    wral
    #
    vw
    cr
    wrex
    #
    vy
    cr
    wrex
    #
    @0
    @4
    @5
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    wi
    #
    vz
    @10
    wral
    #
    vy
    cr
    wrex
    @13
    @0
    vy
    vz
    @10
    @5
    cA
    c1
    cc
    @0
    @5
    cc
    wcel
    #
    vz
    @10
    @0
    @10
    cc
    @3
    cF
    cA
    cF
    rlimf
    #
    ffvelrnda
    #
    ralrimiva
    c1
    crp
    wcel
    @0
    1rp
    a1i
    @0
    cF
    vz
    @10
    @5
    cmpt
    cA
    crli
    @0
    vz
    @10
    cc
    cF
    @20
    feqmptd
    @0
    id
    eqbrtrrd
    rlimi
    @0
    @18
    @12
    vy
    cr
    @0
    @2
    cr
    wcel
    #
    wa
    #
    cA
    cabs
    cfv
    #
    c1
    caddc
    co
    #
    cr
    wcel
    #
    @18
    @4
    @6
    @25
    cle
    wbr
    #
    wi
    #
    vz
    @10
    wral
    #
    @12
    @23
    @24
    cr
    wcel
    #
    @26
    @23
    cA
    @0
    cA
    cc
    wcel
    #
    @22
    cA
    cF
    rlimcl
    adantr
    #
    abscld
    #
    @24
    peano2re
    syl
    #
    @23
    @17
    @28
    vz
    @10
    @23
    @3
    @10
    wcel
    #
    wa
    #
    @16
    @27
    @4
    @36
    @16
    @6
    @25
    clt
    wbr
    #
    @27
    @36
    @16
    @6
    @24
    cmin
    co
    #
    c1
    clt
    wbr
    #
    @37
    @36
    @38
    @15
    cle
    wbr
    #
    @16
    @39
    @36
    @5
    cA
    @0
    @35
    @19
    @22
    @21
    adantlr
    #
    @23
    @31
    @35
    @32
    adantr
    #
    abs2difd
    @36
    @38
    cr
    wcel
    @15
    cr
    wcel
    c1
    cr
    wcel
    @40
    @16
    wa
    @39
    wi
    @36
    @6
    @24
    @36
    @5
    @41
    abscld
    #
    @23
    @30
    @35
    @33
    adantr
    #
    resubcld
    @36
    @14
    @36
    @5
    cA
    @41
    @42
    subcld
    abscld
    @36
    1red
    #
    @38
    @15
    c1
    lelttr
    syl3anc
    mpand
    @36
    @6
    @24
    c1
    @43
    @44
    @45
    ltsubadd2d
    sylibd
    @36
    @6
    cr
    wcel
    @26
    @37
    @27
    wi
    @43
    @23
    @26
    @35
    @34
    adantr
    @6
    @25
    ltle
    syl2anc
    syld
    imim2d
    ralimdva
    @11
    @29
    vw
    @25
    cr
    @7
    @25
    wceq
    #
    @9
    @28
    vz
    @10
    @46
    @8
    @27
    @4
    @7
    @25
    @6
    cle
    breq2
    imbi2d
    ralbidv
    rspcev
    syl6an
    reximdva
    mpd
    @0
    @10
    cc
    cF
    wf
    @10
    cr
    wss
    @1
    @13
    wb
    @20
    cA
    cF
    rlimss
    vy
    vz
    @10
    vw
    cF
    elo12
    syl2anc
    mpbird
end
