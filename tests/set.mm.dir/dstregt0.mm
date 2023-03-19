include "cim.mm"
include "cfv.mm"
include "cabs.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "crp.mm"
include "wcel.mm"
include "cv.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wral.mm"
include "wrex.mm"
include "cc.mm"
include "eldifad.mm"
include "imcld.mm"
include "recnd.mm"
include "cc0.mm"
include "wceq.mm"
include "eldifbd.mm"
include "wb.mm"
include "reim0b.mm"
include "syl.mm"
include "mtbid.mm"
include "neqned.mm"
include "absrpcld.mm"
include "rphalfcld.mm"
include "wa.mm"
include "adantr.mm"
include "recn.mm"
include "adantl.mm"
include "imsubd.mm"
include "simpr.mm"
include "reim0d.mm"
include "oveq2d.mm"
include "subid1d.mm"
include "3eqtrrd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "eqeltrrd.mm"
include "abscld.mm"
include "rehalfcld.mm"
include "subcld.mm"
include "wne.mm"
include "eqnetrrd.mm"
include "rphalflt.mm"
include "cle.mm"
include "absimle.mm"
include "ltletrd.mm"
include "eqbrtrd.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem dstregt0
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume dstregt0.1: |- ( ph -> A e. ( CC \ RR ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint ph y
  assert |- ( ph -> E. x e. RR+ A. y e. RR x < ( abs ` ( A - y ) ) )

  proof
    wph
    cA
    cim
    cfv
    #
    cabs
    cfv
    #
    c2
    cdiv
    co
    #
    crp
    wcel
    @2
    cA
    vy
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    vy
    cr
    wral
    #
    vx
    cv
    #
    @5
    clt
    wbr
    #
    vy
    cr
    wral
    #
    vx
    crp
    wrex
    wph
    @1
    wph
    @0
    wph
    @0
    wph
    cA
    wph
    cA
    cc
    cr
    dstregt0.1
    eldifad
    #
    imcld
    recnd
    #
    wph
    @0
    cc0
    wph
    cA
    cr
    wcel
    #
    @0
    cc0
    wceq
    #
    wph
    cA
    cc
    cr
    dstregt0.1
    eldifbd
    wph
    cA
    cc
    wcel
    #
    @13
    @14
    wb
    @11
    cA
    reim0b
    syl
    mtbid
    neqned
    #
    absrpcld
    rphalfcld
    wph
    @6
    vy
    cr
    wph
    @3
    cr
    wcel
    #
    wa
    #
    @2
    @4
    cim
    cfv
    #
    cabs
    cfv
    #
    c2
    cdiv
    co
    #
    @5
    clt
    @18
    @1
    @20
    c2
    cdiv
    @18
    @0
    @19
    cabs
    @18
    @19
    @0
    @3
    cim
    cfv
    #
    cmin
    co
    @0
    cc0
    cmin
    co
    @0
    @18
    cA
    @3
    wph
    @15
    @17
    @11
    adantr
    #
    @17
    @3
    cc
    wcel
    wph
    @3
    recn
    adantl
    #
    imsubd
    @18
    @22
    cc0
    @0
    cmin
    @18
    @3
    wph
    @17
    simpr
    reim0d
    oveq2d
    @18
    @0
    wph
    @0
    cc
    wcel
    @17
    @12
    adantr
    #
    subid1d
    3eqtrrd
    #
    fveq2d
    oveq1d
    @18
    @21
    @20
    @5
    @18
    @20
    @18
    @19
    @18
    @0
    @19
    cc
    @26
    @25
    eqeltrrd
    #
    abscld
    #
    rehalfcld
    @28
    @18
    @4
    @18
    cA
    @3
    @23
    @24
    subcld
    #
    abscld
    @18
    @20
    crp
    wcel
    @21
    @20
    clt
    wbr
    @18
    @19
    @27
    @18
    @0
    @19
    cc0
    @26
    wph
    @0
    cc0
    wne
    @17
    @16
    adantr
    eqnetrrd
    absrpcld
    @20
    rphalflt
    syl
    @18
    @4
    cc
    wcel
    @20
    @5
    cle
    wbr
    @29
    @4
    absimle
    syl
    ltletrd
    eqbrtrd
    ralrimiva
    @10
    @7
    vx
    @2
    crp
    @8
    @2
    wceq
    @9
    @6
    vy
    cr
    @8
    @2
    @5
    clt
    breq1
    ralbidv
    rspcev
    syl2anc
end
