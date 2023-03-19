include "cvv.mm"
include "wcel.mm"
include "cmpt.mm"
include "csupp.mm"
include "co.mm"
include "wss.mm"
include "wi.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "eqid.mm"
include "adantl.mm"
include "simpl.mm"
include "mptsuppdifd.mm"
include "cv.mm"
include "wne.mm"
include "eldifsni.mm"
include "wn.mm"
include "wceq.mm"
include "eldif.mm"
include "adantll.mm"
include "sylan2br.mm"
include "expr.mm"
include "necon1ad.mm"
include "syl5.mm"
include "3impia.mm"
include "rabssdv.mm"
include "eqsstrd.mm"
include "ex.mm"
include "c0.mm"
include "id.mm"
include "intnand.mm"
include "supp0prc.mm"
include "syl.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem suppss2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume suppss2.n: |- ( ( ph /\ k e. ( A \ W ) ) -> B = Z )
  assume suppss2.a: |- ( ph -> A e. V )

  disjoint A k
  disjoint k ph
  disjoint W k
  disjoint Z k
  assert |- ( ph -> ( ( k e. A |-> B ) supp Z ) C_ W )

  proof
    cZ
    cvv
    wcel
    #
    wph
    vk
    cA
    cB
    cmpt
    #
    cZ
    csupp
    co
    #
    cW
    wss
    #
    wi
    @0
    wph
    @3
    @0
    wph
    wa
    #
    @2
    cB
    cvv
    cZ
    csn
    cdif
    wcel
    #
    vk
    cA
    crab
    cW
    @4
    vk
    cA
    cB
    @1
    cV
    cvv
    cZ
    @1
    eqid
    wph
    cA
    cV
    wcel
    @0
    suppss2.a
    adantl
    @0
    wph
    simpl
    mptsuppdifd
    @4
    @5
    vk
    cA
    cW
    @4
    vk
    cv
    #
    cA
    wcel
    #
    @5
    @6
    cW
    wcel
    #
    @5
    cB
    cZ
    wne
    @4
    @7
    wa
    #
    @8
    cB
    cvv
    cZ
    eldifsni
    @9
    @8
    cB
    cZ
    @4
    @7
    @8
    wn
    #
    cB
    cZ
    wceq
    #
    @7
    @10
    wa
    @4
    @6
    cA
    cW
    cdif
    wcel
    #
    @11
    @6
    cA
    cW
    eldif
    wph
    @12
    @11
    @0
    suppss2.n
    adantll
    sylan2br
    expr
    necon1ad
    syl5
    3impia
    rabssdv
    eqsstrd
    ex
    @0
    wn
    #
    @3
    wph
    @13
    @2
    c0
    cW
    @13
    @1
    cvv
    wcel
    #
    @0
    wa
    wn
    @2
    c0
    wceq
    @13
    @0
    @14
    @13
    id
    intnand
    @1
    cZ
    supp0prc
    syl
    cW
    0ss
    syl6eqss
    a1d
    pm2.61i
end
