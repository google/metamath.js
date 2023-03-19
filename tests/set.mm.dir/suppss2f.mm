include "cmpt.mm"
include "csupp.mm"
include "co.mm"
include "cv.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmptf.mm"
include "oveq1i.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wsb.mm"
include "sbt.mm"
include "sbim.mm"
include "sban.mm"
include "sbf.mm"
include "nfdif.mm"
include "clelsb3f.mm"
include "anbi12i.mm"
include "bitri.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sbceq1g.mm"
include "ax-mp.mm"
include "imbi12i.mm"
include "mpbi.mm"
include "suppss2.mm"
include "syl5eqss.mm"

theorem suppss2f
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vl: setvar l
  assume suppss2f.p: |- F/ k ph
  assume suppss2f.a: |- F/_ k A
  assume suppss2f.w: |- F/_ k W
  assume suppss2f.n: |- ( ( ph /\ k e. ( A \ W ) ) -> B = Z )
  assume suppss2f.v: |- ( ph -> A e. V )

  disjoint Z k
  disjoint A l
  disjoint B l
  disjoint W l
  disjoint k l
  disjoint Z l
  disjoint l ph
  assert |- ( ph -> ( ( k e. A |-> B ) supp Z ) C_ W )

  proof
    wph
    vk
    cA
    cB
    cmpt
    #
    cZ
    csupp
    co
    vl
    cA
    vk
    vl
    cv
    #
    cB
    csb
    #
    cmpt
    #
    cZ
    csupp
    co
    cW
    @0
    @3
    cZ
    csupp
    vk
    vl
    cA
    cB
    @2
    suppss2f.a
    vl
    cA
    nfcv
    vl
    cB
    nfcv
    vk
    @1
    cB
    nfcsb1v
    vk
    @1
    cB
    csbeq1a
    cbvmptf
    oveq1i
    wph
    cA
    @2
    vl
    cV
    cW
    cZ
    wph
    vk
    cv
    cA
    cW
    cdif
    #
    wcel
    #
    wa
    #
    cB
    cZ
    wceq
    #
    wi
    #
    vk
    vl
    wsb
    #
    wph
    @1
    @4
    wcel
    #
    wa
    #
    @2
    cZ
    wceq
    #
    wi
    #
    @8
    vk
    vl
    suppss2f.n
    sbt
    @9
    @6
    vk
    vl
    wsb
    #
    @7
    vk
    vl
    wsb
    #
    wi
    @13
    @6
    @7
    vk
    vl
    sbim
    @14
    @11
    @15
    @12
    @14
    wph
    vk
    vl
    wsb
    #
    @5
    vk
    vl
    wsb
    #
    wa
    @11
    wph
    @5
    vk
    vl
    sban
    @16
    wph
    @17
    @10
    wph
    vk
    vl
    suppss2f.p
    sbf
    vl
    vk
    @4
    vk
    cA
    cW
    suppss2f.a
    suppss2f.w
    nfdif
    clelsb3f
    anbi12i
    bitri
    @15
    @7
    vk
    @1
    wsbc
    #
    @12
    @7
    vk
    vl
    sbsbc
    @1
    cvv
    wcel
    @18
    @12
    wb
    vl
    vex
    vk
    @1
    cB
    cZ
    cvv
    sbceq1g
    ax-mp
    bitri
    imbi12i
    bitri
    mpbi
    suppss2f.v
    suppss2
    syl5eqss
end
