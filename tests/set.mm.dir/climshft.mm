include "wcel.mm"
include "cz.mm"
include "cshi.mm"
include "co.mm"
include "cli.mm"
include "wbr.mm"
include "wb.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq1d.mm"
include "breq1.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "cneg.mm"
include "znegcl.mm"
include "ovex.mm"
include "climshftlem.mm"
include "syl.mm"
include "cvv.mm"
include "cuz.mm"
include "cfv.mm"
include "eqid.mm"
include "ovexd.mm"
include "vex.mm"
include "a1i.mm"
include "id.mm"
include "cc.mm"
include "zcn.mm"
include "eluzelcn.mm"
include "shftcan1.mm"
include "syl2an.mm"
include "climeq.mm"
include "sylibd.mm"
include "impbid.mm"
include "vtoclg.mm"
include "impcom.mm"

theorem climshft
  let cA: class A
  let cF: class F
  let cM: class M
  let cV: class V
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x


  assert |- ( ( M e. ZZ /\ F e. V ) -> ( ( F shift M ) ~~> A <-> F ~~> A ) )

  proof
    cF
    cV
    wcel
    cM
    cz
    wcel
    #
    cF
    cM
    cshi
    co
    #
    cA
    cli
    wbr
    #
    cF
    cA
    cli
    wbr
    #
    wb
    #
    @0
    vf
    cv
    #
    cM
    cshi
    co
    #
    cA
    cli
    wbr
    #
    @5
    cA
    cli
    wbr
    #
    wb
    #
    wi
    @0
    @4
    wi
    vf
    cF
    cV
    @5
    cF
    wceq
    #
    @9
    @4
    @0
    @10
    @7
    @2
    @8
    @3
    @10
    @6
    @1
    cA
    cli
    @5
    cF
    cM
    cshi
    oveq1
    breq1d
    @5
    cF
    cA
    cli
    breq1
    bibi12d
    imbi2d
    @0
    @7
    @8
    @0
    @7
    @6
    cM
    cneg
    #
    cshi
    co
    #
    cA
    cli
    wbr
    #
    @8
    @0
    @11
    cz
    wcel
    @7
    @13
    wi
    cM
    znegcl
    cA
    @6
    @11
    @5
    cM
    cshi
    ovex
    climshftlem
    syl
    @0
    cA
    vk
    @12
    @5
    cM
    cvv
    cvv
    cM
    cuz
    cfv
    #
    @14
    eqid
    @0
    @6
    @11
    cshi
    ovexd
    @5
    cvv
    wcel
    @0
    vf
    vex
    #
    a1i
    @0
    id
    @0
    cM
    cc
    wcel
    vk
    cv
    #
    cc
    wcel
    @16
    @12
    cfv
    @16
    @5
    cfv
    wceq
    @16
    @14
    wcel
    cM
    zcn
    cM
    @16
    eluzelcn
    cM
    @16
    @5
    @15
    shftcan1
    syl2an
    climeq
    sylibd
    cA
    @5
    cM
    @15
    climshftlem
    impbid
    vtoclg
    impcom
end
