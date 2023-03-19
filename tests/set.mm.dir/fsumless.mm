include "csu.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "cc0.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "difss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "cv.mm"
include "cr.mm"
include "eldifi.mm"
include "sylan2.mm"
include "fsumge0.mm"
include "syl2anc.mm"
include "sselda.mm"
include "syldan.mm"
include "fsumrecl.mm"
include "addge01d.mm"
include "mpbid.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjdif.mm"
include "a1i.mm"
include "cun.mm"
include "undif.mm"
include "sylib.mm"
include "eqcomd.mm"
include "wa.mm"
include "recnd.mm"
include "fsumsplit.mm"
include "breqtrrd.mm"

theorem fsumless
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  assume fsumge0.1: |- ( ph -> A e. Fin )
  assume fsumge0.2: |- ( ( ph /\ k e. A ) -> B e. RR )
  assume fsumge0.3: |- ( ( ph /\ k e. A ) -> 0 <_ B )
  assume fsumless.4: |- ( ph -> C C_ A )

  disjoint A k
  disjoint C k
  disjoint k ph
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint M k
  disjoint m ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> sum_ k e. C B <_ sum_ k e. A B )

  proof
    wph
    cC
    cB
    vk
    csu
    #
    @0
    cA
    cC
    cdif
    #
    cB
    vk
    csu
    #
    caddc
    co
    #
    cA
    cB
    vk
    csu
    cle
    wph
    cc0
    @2
    cle
    wbr
    @0
    @3
    cle
    wbr
    wph
    @1
    cB
    vk
    wph
    cA
    cfn
    wcel
    #
    @1
    cA
    wss
    @1
    cfn
    wcel
    fsumge0.1
    cA
    cC
    difss
    cA
    @1
    ssfi
    sylancl
    #
    vk
    cv
    #
    @1
    wcel
    #
    wph
    @6
    cA
    wcel
    #
    cB
    cr
    wcel
    #
    @6
    cA
    cC
    eldifi
    #
    fsumge0.2
    sylan2
    #
    @7
    wph
    @8
    cc0
    cB
    cle
    wbr
    @10
    fsumge0.3
    sylan2
    fsumge0
    wph
    @0
    @2
    wph
    cC
    cB
    vk
    wph
    @4
    cC
    cA
    wss
    #
    cC
    cfn
    wcel
    fsumge0.1
    fsumless.4
    cA
    cC
    ssfi
    syl2anc
    wph
    @6
    cC
    wcel
    @8
    @9
    wph
    cC
    cA
    @6
    fsumless.4
    sselda
    fsumge0.2
    syldan
    fsumrecl
    wph
    @1
    cB
    vk
    @5
    @11
    fsumrecl
    addge01d
    mpbid
    wph
    cC
    @1
    cB
    cA
    vk
    cC
    @1
    cin
    c0
    wceq
    wph
    cC
    cA
    disjdif
    a1i
    wph
    cC
    @1
    cun
    #
    cA
    wph
    @12
    @13
    cA
    wceq
    fsumless.4
    cC
    cA
    undif
    sylib
    eqcomd
    fsumge0.1
    wph
    @8
    wa
    cB
    fsumge0.2
    recnd
    fsumsplit
    breqtrrd
end
